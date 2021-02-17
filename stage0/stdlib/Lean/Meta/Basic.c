// Lean compiler output
// Module: Lean.Meta.Basic
// Imports: Init Lean.Data.LOption Lean.Environment Lean.Class Lean.ReducibilityAttrs Lean.Util.Trace Lean.Util.RecDepth Lean.Util.PPExt Lean.Util.OccursCheck Lean.Compiler.InlineAttrs Lean.Meta.TransparencyMode Lean.Meta.DiscrTreeTypes Lean.Eval Lean.CoreM
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
lean_object* l_Lean_Meta_withConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instBEqInfoCacheKey;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cache_synthInstance___default;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Config_transparency___default;
lean_object* l_Lean_Meta_withLetDecl(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedParamInfo___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1;
size_t l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthPending___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__2(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
uint8_t l_Lean_Meta_Config_zetaNonDep___default;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_synthPending___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1(lean_object*);
lean_object* l_Lean_Meta_mapMetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_InternalExceptionId_toString___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_orelse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2;
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5;
lean_object* l_Lean_Meta_savingCache(lean_object*);
lean_object* l_Lean_Meta_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3;
lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_forallMetaTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run(lean_object*);
uint8_t l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(uint8_t, uint8_t);
lean_object* l_Lean_Meta_mapError(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instOrElseMetaM___closed__1;
lean_object* l_Lean_Meta_occursCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1;
extern lean_object* l_StateRefT_x27_instMonadLiftStateRefT_x27___closed__1;
lean_object* l_Lean_Meta_getLocalDeclFromUserName_match__1(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignment_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1(lean_object*);
uint8_t l_Lean_MetavarContext_isDelayedAssigned(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_State_postponed___default;
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_mctx___default;
lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope(lean_object*);
lean_object* l_Lean_Meta_elimMVarDeps(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getParamNames___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Meta_instInhabitedState___closed__1;
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__1(lean_object*);
lean_object* l_Lean_Meta_forallTelescope(lean_object*);
lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
extern lean_object* l_Std_PersistentHashMap_root___default___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_fullApproxDefEq(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedAssignment_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1(lean_object*);
lean_object* l_Lean_Meta_orelse(lean_object*);
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_zetaFVarIds___default;
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1(lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cache_funInfo___default;
lean_object* l_Lean_Meta_withReducible___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_orelseMergeErrors(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Config_unificationHints___default;
lean_object* l_Lean_Meta_fullApproxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___boxed(lean_object*);
lean_object* l_Lean_Meta_orelseMergeErrors___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___closed__2;
lean_object* l_Lean_Meta_setInlineAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedPersistentArray___closed__1;
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar_match__1(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_whnfI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducibleAndInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__2(lean_object*);
lean_object* l_Lean_Meta_getPostponed___boxed(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3_(lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedCache___closed__1;
lean_object* l_Lean_Meta_mapMetaM(lean_object*);
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
lean_object* l_Lean_Meta_withTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedException___closed__1;
lean_object* l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp_match__1(lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2;
lean_object* l_Lean_Meta_mkFreshTypeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar_match__1(lean_object*);
lean_object* l_Lean_Meta_whnf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cache_synthInstance___default___closed__1;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarWithId_match__1(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__1;
lean_object* l_Lean_Meta_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__2;
lean_object* l_Lean_Meta_instInhabitedMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedCache;
extern lean_object* l_Lean_Compiler_inlineAttrs;
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadEnvCoreM;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Config_isDefEqStuckEx___default;
lean_object* l_Lean_Meta_instMonadLCtxMetaM___closed__3;
lean_object* l_Lean_MetavarContext_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*);
lean_object* l_Lean_Meta_map2MetaM(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__2;
lean_object* l_Lean_Meta_MetaM_toIO(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTrackingZeta___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelAssignment_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___boxed(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__4;
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1;
lean_object* l_Lean_Meta_ParamInfo_isExplicit___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_mkArrow___closed__2;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_renameMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_instMonadLCtxMetaM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1;
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
extern lean_object* l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
lean_object* l_Lean_Meta_instAddMessageContextMetaM___closed__1;
lean_object* l_Lean_Meta_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_liftMetaM___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map2MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___closed__2;
lean_object* l_Lean_Meta_renameMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_hasFwdDeps___default;
extern lean_object* l_Lean_Level_updateSucc_x21___closed__3;
lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducibleAndInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1;
lean_object* l_Lean_Meta_savingCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__1(lean_object*);
lean_object* l_Lean_Meta_orelseMergeErrors___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_instImplicit___default;
lean_object* l_Lean_Meta_setMVarKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2;
lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__1;
uint8_t l_Lean_Meta_Config_constApprox___default;
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process(lean_object*);
lean_object* l_Lean_instMonadEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__3;
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withDefault(lean_object*);
lean_object* l_Lean_Meta_approxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1;
lean_object* l_Lean_Meta_Cache_whnfAll___default;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM(lean_object*);
lean_object* l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_Core_getMaxHeartbeats___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_approxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp(lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Config_ctxApprox___default;
lean_object* l_Lean_Meta_map1MetaM(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5;
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_State_cache___default;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f(lean_object*);
lean_object* l_Lean_Meta_instMonadLCtxMetaM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__2;
lean_object* l_Lean_Meta_ParamInfo_backDeps___default;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3;
uint8_t l_Lean_Meta_Config_quasiPatternApprox___default;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMetaM(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1;
lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withDefault___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3;
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106_(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed__const__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3;
lean_object* l_Lean_Meta_occursCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Meta_mkArrow___closed__1;
lean_object* l_Lean_Meta_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__5;
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__2(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*);
lean_object* l_Lean_Meta_instInhabitedParamInfo;
lean_object* l_Lean_Meta_lambdaLetTelescope(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config___default;
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___closed__1;
lean_object* l_Lean_Meta_isDelayedAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_approxDefEq(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1;
lean_object* l_Lean_Meta_instInhabitedInfoCacheKey;
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls(lean_object*);
uint8_t l_Lean_Meta_Config_foApprox___default;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withDefault___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMetaEvalMetaM(lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__3;
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_toIO_match__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__3;
lean_object* l_Lean_Meta_instInhabitedMetaM___rarg(lean_object*);
lean_object* l_Lean_Meta_FunInfo_paramInfo___default;
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_resultDeps___default;
lean_object* l_Lean_Meta_setMVarKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getParamNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_resetTraceState___rarg___lambda__1___closed__1;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCache(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instBEqInfoCacheKey___closed__1;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM;
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4;
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux_match__1(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addExprMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_instOrElseMetaM(lean_object*);
lean_object* l_Lean_Meta_synthPendingRef;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
lean_object* l_Lean_Meta_Context_lctx___default;
lean_object* l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Config_trackZeta___default;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_Cache_funInfo___default___closed__1;
lean_object* l_Lean_Meta_getTheoremInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1;
lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2;
lean_object* l_Lean_Meta_isExprDefEqAuxRef;
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_object*);
lean_object* l_Lean_Meta_withLCtx(lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducible___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_fullApproxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4;
lean_object* l_Lean_Meta_withAtLeastTransparency(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl(lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadLCtxMetaM___closed__1;
lean_object* l_Lean_Meta_instMonadLCtxMetaM___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_modifyPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_restoreSynthInstanceCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDelayedAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Meta_Context_config___default___closed__1;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars_match__1(lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedState;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cache_inferType___default___closed__1;
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_modifyPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withConfig(lean_object*);
lean_object* l_Lean_Meta_Cache_whnfDefault___default;
lean_object* l_Lean_Meta_withReducibleAndInstances(lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_occursCheck(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_toIO_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnumAttributes_setValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process_match__1(lean_object*);
lean_object* l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp(lean_object*);
lean_object* l_Lean_Meta_withTrackingZeta___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedInfoCacheKey___closed__1;
lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute_match__1(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTrackingZeta(lean_object*);
extern lean_object* l_Lean_Core_State_ngen___default___closed__1;
lean_object* l_Lean_Meta_getLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_localInstances___default;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTheoremInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cache_funInfo___default___closed__2;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__2(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_implicit___default;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadLCtxMetaM;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed(lean_object*);
lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__2(lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance(lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName___closed__2;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducible(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars_match__1(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__1(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1;
lean_object* l_Lean_Meta_Cache_inferType___default;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_Meta_mapError___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLevel;
lean_object* l_Lean_Meta_getFVarLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMkBindingM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignableMVar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1(lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEqStuck");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lean_Meta_Config_foApprox___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_ctxApprox___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_quasiPatternApprox___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_constApprox___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_isDefEqStuckEx___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_transparency___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_zetaNonDep___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_trackZeta___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_unificationHints___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ParamInfo_implicit___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ParamInfo_instImplicit___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ParamInfo_hasFwdDeps___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ParamInfo_backDeps___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedParamInfo___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedParamInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedParamInfo___closed__1;
return x_1;
}
}
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_Meta_ParamInfo_isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_ParamInfo_isExplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_FunInfo_paramInfo___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_FunInfo_resultDeps___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_instInhabitedExpr___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInfoCacheKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedInfoCacheKey___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(x_5);
x_12 = lean_box(x_8);
x_13 = lean_apply_6(x_3, x_11, x_6, x_7, x_12, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106__match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_expr_eqv(x_4, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1(x_5, x_8);
return x_13;
}
}
}
}
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_580____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instBEqInfoCacheKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_106____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqInfoCacheKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqInfoCacheKey___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey_match__1___rarg), 2, 0);
return x_2;
}
}
size_t l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_6 = l_Lean_Expr_hash(x_3);
if (lean_obj_tag(x_4) == 0)
{
size_t x_7; size_t x_8; size_t x_9; 
x_7 = 11;
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_usize_of_nat(x_10);
x_12 = 13;
x_13 = lean_usize_mix_hash(x_11, x_12);
x_14 = lean_usize_mix_hash(x_6, x_13);
x_15 = lean_usize_mix_hash(x_5, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_inferType___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_root___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_inferType___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_funInfo___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_funInfo___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_root___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_funInfo___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_funInfo___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_synthInstance___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_root___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_synthInstance___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_whnfDefault___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_whnfAll___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__1;
x_2 = l_Lean_Meta_Cache_funInfo___default___closed__2;
x_3 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCache___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_mctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_cache___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCache___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_zetaFVarIds___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_postponed___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_2 = l_Lean_Meta_instInhabitedCache___closed__1;
x_3 = l_Lean_NameSet_empty;
x_4 = l_Std_instInhabitedPersistentArray___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedState___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_config___default___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_1);
lean_ctor_set_uint8(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, 5, x_2);
lean_ctor_set_uint8(x_4, 6, x_3);
lean_ctor_set_uint8(x_4, 7, x_1);
lean_ctor_set_uint8(x_4, 8, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Context_config___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_lctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_mkEmpty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_localInstances___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_instInhabitedMetaM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedException___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_instInhabitedMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_instInhabitedMetaM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_instMonadLCtxMetaM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_instMonadLCtxMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadLCtxMetaM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadLCtxMetaM___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadLCtxMetaM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadLCtxMetaM___closed__1;
x_2 = l_Lean_Meta_instMonadLCtxMetaM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMonadLCtxMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instMonadLCtxMetaM___closed__3;
return x_1;
}
}
lean_object* l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_read___at_Lean_Meta_instMonadLCtxMetaM___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_instMonadLCtxMetaM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instMonadLCtxMetaM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_get(x_2, x_7);
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
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_26 = lean_apply_1(x_1, x_22);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_11);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMCtxMetaM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMCtxMetaM___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadMCtxMetaM___closed__1;
x_2 = l_Lean_Meta_instMonadMCtxMetaM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMCtxMetaM___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadMCtxMetaM___closed__3;
x_2 = l_Lean_Meta_instMonadMCtxMetaM___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMCtxMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instMonadMCtxMetaM___closed__5;
return x_1;
}
}
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_instMonadMCtxMetaM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instMonadMCtxMetaM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instMonadMCtxMetaM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_5, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_inc(x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Meta_instAddMessageContextMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instAddMessageContextMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instAddMessageContextMetaM___closed__1;
return x_1;
}
}
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_MetaM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_mk_ref(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_10);
x_12 = lean_apply_5(x_1, x_2, x_10, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_10, x_16);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_MetaM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MetaM_run___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
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
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
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
lean_object* l_Lean_Meta_MetaM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MetaM_toIO_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_MetaM_toIO_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_toIO_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_get_num_heartbeats(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_8);
x_12 = lean_st_mk_ref(x_3, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_MetaM_run___rarg(x_1, x_4, x_5, x_2, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_13);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_toString(x_39, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_15, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_37, 0);
lean_inc(x_54);
lean_dec(x_37);
x_55 = l_Nat_repr(x_54);
x_56 = l_Lean_InternalExceptionId_toString___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_15, 0, x_58);
return x_15;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_dec(x_15);
x_60 = lean_ctor_get(x_37, 0);
lean_inc(x_60);
lean_dec(x_37);
x_61 = l_Nat_repr(x_60);
x_62 = l_Lean_InternalExceptionId_toString___closed__1;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
x_68 = lean_ctor_get(x_2, 2);
x_69 = lean_ctor_get(x_2, 3);
x_70 = lean_ctor_get(x_2, 4);
x_71 = lean_ctor_get(x_2, 5);
x_72 = lean_ctor_get(x_2, 7);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_69);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_73, 5, x_71);
lean_ctor_set(x_73, 6, x_8);
lean_ctor_set(x_73, 7, x_72);
x_74 = lean_st_mk_ref(x_3, x_9);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_75);
x_77 = l_Lean_Meta_MetaM_run___rarg(x_1, x_4, x_5, x_73, x_75, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_75, x_79);
lean_dec(x_75);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_75);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_dec(x_77);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_MessageData_toString(x_92, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_97, 0, x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_96;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_90, 0);
lean_inc(x_105);
lean_dec(x_90);
x_106 = l_Nat_repr(x_105);
x_107 = l_Lean_InternalExceptionId_toString___closed__1;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_103);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_7);
if (x_111 == 0)
{
return x_7;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_7, 0);
x_113 = lean_ctor_get(x_7, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_7);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
lean_object* l_Lean_Meta_MetaM_toIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_toIO___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Context_config___default___closed__1;
x_2 = l_Lean_LocalContext_mkEmpty___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_2 = l_Lean_Meta_instInhabitedCache___closed__1;
x_3 = l_Lean_NameSet_empty;
x_4 = l_Std_PersistentArray_empty___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___at_Lean_Core_getMaxHeartbeats___spec__1(x_3, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Core_getMaxHeartbeats(x_3);
x_33 = l_Lean_Unhygienic_run___rarg___closed__2;
x_34 = l_Lean_Core_State_ngen___default___closed__1;
x_35 = l_Lean_resetTraceState___rarg___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_io_get_num_heartbeats(x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_box(0);
x_42 = lean_box(0);
lean_inc(x_3);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_30);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_31);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_43, 7, x_32);
x_44 = lean_st_mk_ref(x_36, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
x_48 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
lean_inc(x_45);
lean_inc(x_43);
x_49 = l_Lean_Meta_MetaM_run_x27___rarg(x_4, x_47, x_48, x_43, x_45, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_45);
x_52 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_43, x_45, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_45, x_53);
lean_dec(x_45);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_apply_5(x_1, x_57, x_3, x_50, x_59, x_56);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_dec(x_52);
x_7 = x_61;
x_8 = x_62;
goto block_28;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_65 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_43, x_45, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_7 = x_63;
x_8 = x_66;
goto block_28;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_7 = x_67;
x_8 = x_68;
goto block_28;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_37);
if (x_69 == 0)
{
return x_37;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_37, 0);
x_71 = lean_ctor_get(x_37, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_37);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_28:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_MessageData_toString(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_10, 1);
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
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_Nat_repr(x_22);
x_24 = l_Lean_InternalExceptionId_toString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_instMetaEvalMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instMetaEvalMetaM___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Meta_instMetaEvalMetaM___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isDefEqStuckExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_throwIsDefEqStuck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_throwIsDefEqStuck___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_throwIsDefEqStuck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_throwIsDefEqStuck(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Meta_liftMetaM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_liftMetaM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_liftMetaM___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_mapMetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_mapMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mapMetaM___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_mapMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mapMetaM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_1, x_3);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg___lambda__1), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_map1MetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg___lambda__2), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_map1MetaM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_3, x_4);
x_11 = lean_apply_7(x_2, lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_map2MetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__2), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_map2MetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg), 5, 0);
return x_4;
}
}
lean_object* l_Lean_Meta_getLocalInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getLocalInstances(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_getConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getConfig(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_setMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
x_14 = lean_st_ref_set(x_3, x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_11);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_Meta_setMCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_setMCtx(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
lean_dec(x_11);
x_12 = l_Lean_NameSet_empty;
lean_ctor_set(x_8, 2, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = l_Lean_NameSet_empty;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = lean_st_ref_set(x_1, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resetZetaFVarIds___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_resetZetaFVarIds___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_resetZetaFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
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
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Meta_getZetaFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getZetaFVarIds___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaFVarIds___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getZetaFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
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
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Meta_getPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getPostponed___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_setPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 3);
lean_dec(x_13);
lean_ctor_set(x_10, 3, x_1);
x_14 = lean_st_ref_set(x_3, x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_1);
x_25 = lean_st_ref_set(x_3, x_24, x_11);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_Meta_setPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_setPostponed(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_modifyPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 3);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_10, 3, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_26 = lean_apply_1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_11);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
lean_object* l_Lean_Meta_modifyPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_modifyPostponed(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf implementation was not set");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferType implementation was not set");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq implementation was not set");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3;
x_9 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Meta_whnf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_whnfRef;
x_16 = lean_st_ref_get(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_6(x_17, x_2, x_4, x_5, x_6, x_7, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_get(x_7, x_8);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_whnfRef;
x_31 = lean_st_ref_get(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_2, x_4, x_5, x_27, x_7, x_33);
return x_34;
}
}
}
lean_object* l_Lean_Meta_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_whnf___lambda__1(x_7, x_1, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_whnf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_whnf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_whnfForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_isForall(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_inferType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_inferTypeRef;
x_16 = lean_st_ref_get(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_6(x_17, x_2, x_4, x_5, x_6, x_7, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_get(x_7, x_8);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_inferTypeRef;
x_31 = lean_st_ref_get(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_2, x_4, x_5, x_27, x_7, x_33);
return x_34;
}
}
}
lean_object* l_Lean_Meta_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_inferType___lambda__1(x_7, x_1, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_inferType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_inferType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_isExprDefEqAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
x_14 = lean_st_ref_get(x_8, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_isExprDefEqAuxRef;
x_17 = lean_st_ref_get(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_apply_7(x_18, x_2, x_3, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set(x_28, 6, x_26);
lean_ctor_set(x_28, 7, x_27);
x_29 = lean_st_ref_get(x_8, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Meta_isExprDefEqAuxRef;
x_32 = lean_st_ref_get(x_31, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_apply_7(x_33, x_2, x_3, x_5, x_6, x_28, x_8, x_34);
return x_35;
}
}
}
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_isExprDefEqAux___lambda__1(x_8, x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEqAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isExprDefEqAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_synthPending___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_synthPendingRef;
x_16 = lean_st_ref_get(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_6(x_17, x_2, x_4, x_5, x_6, x_7, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_get(x_7, x_8);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_synthPendingRef;
x_31 = lean_st_ref_get(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_2, x_4, x_5, x_27, x_7, x_33);
return x_34;
}
}
}
lean_object* l_Lean_Meta_synthPending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_synthPending___lambda__1(x_7, x_1, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_synthPending___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_synthPending___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
x_14 = lean_apply_7(x_2, lean_box(0), x_3, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_apply_7(x_2, lean_box(0), x_3, x_5, x_6, x_22, x_8, x_9);
return x_23;
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_withIncRecDepth___rarg___lambda__1(x_8, x_2, x_1, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___rarg___lambda__2), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withIncRecDepth___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_1);
x_20 = l_Lean_MetavarContext_addExprMVarDecl(x_19, x_1, x_6, x_2, x_3, x_4, x_5, x_7);
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_9, x_16, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_Lean_mkMVar(x_1);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_mkMVar(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
lean_inc(x_1);
x_32 = l_Lean_MetavarContext_addExprMVarDecl(x_28, x_1, x_6, x_2, x_3, x_4, x_5, x_7);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = lean_st_ref_set(x_9, x_33, x_17);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Lean_mkMVar(x_1);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_14;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_name_mk_numeral(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_15);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_name_mk_numeral(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_32, x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_take(x_1, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_42);
x_45 = lean_st_ref_set(x_1, x_44, x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_mkFreshExprMVarAt(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_get(x_3, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_6);
x_15 = l_Lean_MetavarContext_addLevelMVarDecl(x_14, x_6);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_1, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Lean_mkLevelMVar(x_6);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_mkLevelMVar(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_6);
x_27 = l_Lean_MetavarContext_addLevelMVarDecl(x_23, x_6);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = l_Lean_mkLevelMVar(x_6);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVar___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkFreshLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Meta_mkFreshExprMVarAt(x_9, x_11, x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_4);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkSort(x_10);
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_mkFreshExprMVar(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_mkSort(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_mkFreshTypeMVar(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(x_1, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_6);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVarWithId_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkSort(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = 0;
x_16 = lean_box(0);
lean_inc(x_5);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(x_1, x_18, x_3, x_4, x_20, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(x_1, x_22, x_3, x_4, x_23, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_mkFreshExprMVarWithId(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_getTransparency(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_getConfig(x_1, x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_8, 5);
lean_dec(x_8);
x_10 = lean_box(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get_uint8(x_11, 5);
lean_dec(x_11);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
lean_object* l_Lean_Meta_getTransparency___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getTransparency(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_shouldReduceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_getTransparency(x_1, x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = 0;
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_10, x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = 0;
x_16 = lean_unbox(x_13);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_16, x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
lean_object* l_Lean_Meta_shouldReduceAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_shouldReduceAll(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_getTransparency(x_1, x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = 2;
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_10, x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = 2;
x_16 = lean_unbox(x_13);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_16, x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_shouldReduceReducibleOnly(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_getMVarDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_getMVarDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown metavariable '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getMVarDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getMVarDecl___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MetavarContext_findDecl_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_15 = l_Lean_mkMVar(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_getMVarDecl___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(x_20, x_2, x_3, x_4, x_5, x_12);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_MetavarContext_findDecl_x3f(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = l_Lean_mkMVar(x_1);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_getMVarDecl___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_KernelException_toMessageData___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(x_32, x_2, x_3, x_4, x_5, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_setMVarKind(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_setMVarKind(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l_Lean_MetavarContext_setMVarKind(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_setMVarKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_setMVarKind(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_setMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_setMVarType(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l_Lean_MetavarContext_setMVarType(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_setMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_setMVarType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_8, 3);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_8, 3);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyExprMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 2)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_st_ref_get(x_5, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_3, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_8, 3);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_8, 3);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyLevelMVar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_isReadOnlyLevelMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe metavariable '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isReadOnlyLevelMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isReadOnlyLevelMVar___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = l_Lean_MetavarContext_findLevelDepth_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_free_object(x_9);
x_15 = l_Lean_mkLevelMVar(x_1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_isReadOnlyLevelMVar___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(x_20, x_2, x_3, x_4, x_5, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_31);
x_32 = l_Lean_MetavarContext_findLevelDepth_x3f(x_31, x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
x_33 = l_Lean_mkLevelMVar(x_1);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_isReadOnlyLevelMVar___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_KernelException_toMessageData___closed__3;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____spec__1(x_38, x_2, x_3, x_4, x_5, x_30);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_nat_dec_eq(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
return x_48;
}
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyLevelMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_renameMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_renameMVar(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l_Lean_MetavarContext_renameMVar(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_renameMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_renameMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MetavarContext_isExprAssigned(x_12, x_1);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MetavarContext_isExprAssigned(x_17, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isExprMVarAssigned(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MetavarContext_getExprAssignment_x3f(x_12, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MetavarContext_getExprAssignment_x3f(x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getExprMVarAssignment_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_occursCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MetavarContext_occursCheck(x_13, x_1, x_2);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MetavarContext_occursCheck(x_18, x_1, x_2);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
lean_object* l_Lean_Meta_occursCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_occursCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_assignExpr(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l_Lean_MetavarContext_assignExpr(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_assignExprMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_isDelayedAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MetavarContext_isDelayedAssigned(x_12, x_1);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MetavarContext_isDelayedAssigned(x_17, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
lean_object* l_Lean_Meta_isDelayedAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isDelayedAssigned(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MetavarContext_getDelayedAssignment_x3f(x_12, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MetavarContext_getDelayedAssignment_x3f(x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getDelayedAssignment_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MetavarContext_hasAssignableMVar(x_12, x_1);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MetavarContext_hasAssignableMVar(x_17, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_hasAssignableMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown free variable '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownFVar___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_mkFVar(x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Meta_throwUnknownFVar___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_KernelException_toMessageData___closed__3;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
lean_object* l_Lean_Meta_throwUnknownFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwUnknownFVar___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_findLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_local_ctx_find(x_7, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_Meta_findLocalDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_findLocalDecl_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_getLocalDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_local_ctx_find(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
lean_object* l_Lean_Meta_getLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_fvarId_x21(x_1);
x_8 = l_Lean_Meta_getLocalDecl(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFVarLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalDeclFromUserName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_getLocalDeclFromUserName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDeclFromUserName_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_getLocalDeclFromUserName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown local declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getLocalDeclFromUserName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getLocalDeclFromUserName___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_local_ctx_find_from_user_name(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_getLocalDeclFromUserName___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_KernelException_toMessageData___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalDeclFromUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLocalDeclFromUserName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
x_14 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_apply_5(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_level_update_succ(x_1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint64(x_23, sizeof(void*)*1, x_22);
x_24 = lean_level_update_succ(x_23, x_20);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_29 = x_1;
} else {
 lean_dec_ref(x_1);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 8);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set_uint64(x_30, sizeof(void*)*1, x_28);
x_31 = lean_level_update_succ(x_30, x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_15, 0);
lean_dec(x_34);
x_35 = l_Lean_instInhabitedLevel;
x_36 = l_Lean_Level_updateSucc_x21___closed__3;
x_37 = lean_panic_fn(x_35, x_36);
lean_ctor_set(x_15, 0, x_37);
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec(x_15);
x_39 = l_Lean_instInhabitedLevel;
x_40 = l_Lean_Level_updateSucc_x21___closed__3;
x_41 = lean_panic_fn(x_39, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_10, x_11, x_12, x_13, x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_3, x_10, x_11, x_12, x_13, x_14);
x_20 = lean_apply_5(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_level_update_max(x_1, x_17, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_29 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint64(x_29, sizeof(void*)*2, x_28);
x_30 = lean_level_update_max(x_29, x_17, x_25);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(2, 2, 8);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_35);
x_38 = lean_level_update_max(x_37, x_17, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_20, 0);
lean_dec(x_41);
x_42 = l_Lean_instInhabitedLevel;
x_43 = l_Lean_Level_updateMax_x21___closed__3;
x_44 = lean_panic_fn(x_42, x_43);
lean_ctor_set(x_20, 0, x_44);
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = l_Lean_instInhabitedLevel;
x_47 = l_Lean_Level_updateMax_x21___closed__3;
x_48 = lean_panic_fn(x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_10, x_11, x_12, x_13, x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_3, x_10, x_11, x_12, x_13, x_14);
x_20 = lean_apply_5(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_level_update_imax(x_1, x_17, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_29 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint64(x_29, sizeof(void*)*2, x_28);
x_30 = lean_level_update_imax(x_29, x_17, x_25);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(3, 2, 8);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_35);
x_38 = lean_level_update_imax(x_37, x_17, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_20, 0);
lean_dec(x_41);
x_42 = l_Lean_instInhabitedLevel;
x_43 = l_Lean_Level_updateIMax_x21___closed__3;
x_44 = lean_panic_fn(x_42, x_43);
lean_ctor_set(x_20, 0, x_44);
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = l_Lean_instInhabitedLevel;
x_47 = l_Lean_Level_updateIMax_x21___closed__3;
x_48 = lean_panic_fn(x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Level_hasMVar(x_17);
if (x_18 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
x_19 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
x_24 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_17, x_19, x_20, x_21, x_22, x_23);
lean_inc(x_7);
lean_inc(x_5);
x_25 = lean_apply_5(x_24, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_7, x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_5, x_29);
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
lean_inc(x_26);
x_35 = l_Lean_MetavarContext_assignLevel(x_34, x_2, x_26);
lean_ctor_set(x_31, 0, x_35);
x_36 = lean_st_ref_set(x_5, x_31, x_32);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_26);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
x_43 = lean_ctor_get(x_31, 2);
x_44 = lean_ctor_get(x_31, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
lean_inc(x_26);
x_45 = l_Lean_MetavarContext_assignLevel(x_41, x_2, x_26);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
x_47 = lean_st_ref_set(x_5, x_46, x_32);
lean_dec(x_5);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_25);
if (x_51 == 0)
{
return x_25;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_25, 0);
x_53 = lean_ctor_get(x_25, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_25);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_57, x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Level_hasMVar(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_64 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_65 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_66 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_67 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
x_68 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_60, x_63, x_64, x_65, x_66, x_67);
lean_inc(x_7);
lean_inc(x_5);
x_69 = lean_apply_5(x_68, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_7, x_71);
lean_dec(x_7);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_take(x_5, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
lean_inc(x_70);
x_82 = l_Lean_MetavarContext_assignLevel(x_77, x_2, x_70);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 4, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_80);
x_84 = lean_st_ref_set(x_5, x_83, x_76);
lean_dec(x_5);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_70);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_88 = lean_ctor_get(x_69, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_69, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_90 = x_69;
} else {
 lean_dec_ref(x_69);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1;
x_8 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2;
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3;
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4;
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5;
x_12 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_apply_5(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed), 8, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed), 9, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed), 8, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed), 6, 0);
x_12 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_apply_5(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
x_15 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_apply_6(x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_level_update_succ(x_1, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_23);
x_25 = lean_level_update_succ(x_24, x_21);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 1, 8);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_29);
x_32 = lean_level_update_succ(x_31, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = l_Lean_instInhabitedLevel;
x_37 = l_Lean_Level_updateSucc_x21___closed__3;
x_38 = lean_panic_fn(x_36, x_37);
lean_ctor_set(x_16, 0, x_38);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
x_40 = l_Lean_instInhabitedLevel;
x_41 = l_Lean_Level_updateSucc_x21___closed__3;
x_42 = lean_panic_fn(x_40, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_11, x_12, x_13, x_14, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_apply_6(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_3, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_apply_6(x_20, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_level_update_max(x_1, x_18, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_29);
x_31 = lean_level_update_max(x_30, x_18, x_26);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_37 = x_1;
} else {
 lean_dec_ref(x_1);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(2, 2, 8);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_36);
x_39 = lean_level_update_max(x_38, x_18, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = l_Lean_instInhabitedLevel;
x_44 = l_Lean_Level_updateMax_x21___closed__3;
x_45 = lean_panic_fn(x_43, x_44);
lean_ctor_set(x_21, 0, x_45);
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = l_Lean_instInhabitedLevel;
x_48 = l_Lean_Level_updateMax_x21___closed__3;
x_49 = lean_panic_fn(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_17);
if (x_55 == 0)
{
return x_17;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_17, 0);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_17);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_2, x_11, x_12, x_13, x_14, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_apply_6(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_3, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_apply_6(x_20, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_level_update_imax(x_1, x_18, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_29);
x_31 = lean_level_update_imax(x_30, x_18, x_26);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_37 = x_1;
} else {
 lean_dec_ref(x_1);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(3, 2, 8);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_36);
x_39 = lean_level_update_imax(x_38, x_18, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = l_Lean_instInhabitedLevel;
x_44 = l_Lean_Level_updateIMax_x21___closed__3;
x_45 = lean_panic_fn(x_43, x_44);
lean_ctor_set(x_21, 0, x_45);
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = l_Lean_instInhabitedLevel;
x_48 = l_Lean_Level_updateIMax_x21___closed__3;
x_49 = lean_panic_fn(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_17);
if (x_55 == 0)
{
return x_17;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_17, 0);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_17);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_16, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Level_hasMVar(x_18);
if (x_19 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
x_25 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_18, x_20, x_21, x_22, x_23, x_24);
lean_inc(x_8);
lean_inc(x_6);
x_26 = lean_apply_6(x_25, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_8, x_28);
lean_dec(x_8);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_6, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_27);
x_36 = l_Lean_MetavarContext_assignLevel(x_35, x_2, x_27);
lean_ctor_set(x_32, 0, x_36);
x_37 = lean_st_ref_set(x_6, x_32, x_33);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_27);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
x_44 = lean_ctor_get(x_32, 2);
x_45 = lean_ctor_get(x_32, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
lean_inc(x_27);
x_46 = l_Lean_MetavarContext_assignLevel(x_42, x_2, x_27);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
x_48 = lean_st_ref_set(x_6, x_47, x_33);
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
return x_26;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_58, x_2);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Level_hasMVar(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_65 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_66 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_67 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_68 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
x_69 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_61, x_64, x_65, x_66, x_67, x_68);
lean_inc(x_8);
lean_inc(x_6);
x_70 = lean_apply_6(x_69, x_4, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_get(x_8, x_72);
lean_dec(x_8);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_take(x_6, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
lean_inc(x_71);
x_83 = l_Lean_MetavarContext_assignLevel(x_78, x_2, x_71);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 4, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_81);
x_85 = lean_st_ref_set(x_6, x_84, x_77);
lean_dec(x_6);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_89 = lean_ctor_get(x_70, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_70, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_91 = x_70;
} else {
 lean_dec_ref(x_70);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1;
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2;
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3;
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4;
x_12 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5;
x_13 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_1, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_apply_6(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
x_19 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_12, x_14, x_15, x_16, x_17, x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_apply_6(x_19, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_free_object(x_2);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_39 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_40 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_41 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_42 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_43 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
x_44 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_37, x_39, x_40, x_41, x_42, x_43);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = lean_apply_6(x_44, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_49);
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
lean_dec(x_46);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
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
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 < x_1;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = x_3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = x_13;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_15, x_2, x_22);
x_2 = x_21;
x_3 = x_23;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l_Lean_Expr_isMVar(x_2);
x_13 = lean_st_ref_get(x_9, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MetavarContext_getDelayedAssignment_x3f(x_18, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_20) == 0)
{
if (x_12 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_3);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = x_3;
x_26 = lean_box_usize(x_24);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_25);
x_29 = x_28;
x_30 = lean_apply_6(x_29, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_mkAppN(x_21, x_32);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = l_Lean_mkAppN(x_21, x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = l_Lean_Expr_isLambda(x_42);
if (x_44 == 0)
{
lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_array_get_size(x_3);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = x_3;
x_48 = lean_box_usize(x_46);
x_49 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_50 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_49);
lean_closure_set(x_50, 2, x_47);
x_51 = x_50;
x_52 = lean_apply_6(x_51, x_5, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lean_mkAppN(x_42, x_54);
lean_dec(x_54);
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
x_58 = l_Lean_mkAppN(x_42, x_56);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_42);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = l_Array_reverse___rarg(x_3);
x_65 = l_Lean_Expr_betaRev(x_42, x_64);
lean_dec(x_64);
lean_dec(x_42);
x_66 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_65, x_5, x_6, x_7, x_8, x_9, x_43);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_20);
if (x_67 == 0)
{
return x_20;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_19, 0);
lean_inc(x_71);
lean_dec(x_19);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_array_get_size(x_3);
x_75 = lean_array_get_size(x_72);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_73, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Expr_hasExprMVar(x_78);
if (x_80 == 0)
{
size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_81 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_82 = x_3;
x_83 = lean_box_usize(x_81);
x_84 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_85 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_85, 0, x_83);
lean_closure_set(x_85, 1, x_84);
lean_closure_set(x_85, 2, x_82);
x_86 = x_85;
x_87 = lean_apply_6(x_86, x_5, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_expr_abstract(x_78, x_72);
lean_dec(x_72);
lean_dec(x_78);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_expr_instantiate_rev_range(x_90, x_91, x_75, x_89);
lean_dec(x_90);
x_93 = lean_array_get_size(x_89);
x_94 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_93, x_89, x_75, x_92);
lean_dec(x_89);
lean_dec(x_93);
lean_ctor_set(x_87, 0, x_94);
return x_87;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_87, 0);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_87);
x_97 = lean_expr_abstract(x_78, x_72);
lean_dec(x_72);
lean_dec(x_78);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_expr_instantiate_rev_range(x_97, x_98, x_75, x_95);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
x_101 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_100, x_95, x_75, x_99);
lean_dec(x_95);
lean_dec(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_72);
x_103 = !lean_is_exclusive(x_87);
if (x_103 == 0)
{
return x_87;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_87, 0);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_87);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_72);
x_107 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_108 = x_3;
x_109 = lean_box_usize(x_107);
x_110 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_111 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
lean_closure_set(x_111, 2, x_108);
x_112 = x_111;
x_113 = lean_apply_6(x_112, x_5, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = l_Lean_mkAppN(x_2, x_115);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_113, 0);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_113);
x_119 = l_Lean_mkAppN(x_2, x_117);
lean_dec(x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_113);
if (x_121 == 0)
{
return x_113;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_113, 0);
x_123 = lean_ctor_get(x_113, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_113);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_77);
if (x_125 == 0)
{
return x_77;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_77, 0);
x_127 = lean_ctor_get(x_77, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_77);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
size_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_129 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_130 = x_3;
x_131 = lean_box_usize(x_129);
x_132 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_133 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_133, 0, x_131);
lean_closure_set(x_133, 1, x_132);
lean_closure_set(x_133, 2, x_130);
x_134 = x_133;
x_135 = lean_apply_6(x_134, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = l_Lean_mkAppN(x_2, x_137);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_138);
return x_135;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_135, 0);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_135);
x_141 = l_Lean_mkAppN(x_2, x_139);
lean_dec(x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_135);
if (x_143 == 0)
{
return x_135;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_135);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
}
case 5:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_2, 1);
lean_inc(x_148);
lean_dec(x_2);
x_149 = lean_array_set(x_3, x_4, x_148);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_sub(x_4, x_150);
lean_dec(x_4);
x_2 = x_147;
x_3 = x_149;
x_4 = x_151;
goto _start;
}
default: 
{
uint8_t x_153; lean_object* x_154; 
lean_dec(x_4);
x_153 = l_Lean_Expr_isMVar(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_154 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_154) == 0)
{
if (x_153 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_array_get_size(x_3);
x_158 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_159 = x_3;
x_160 = lean_box_usize(x_158);
x_161 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_162 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_162, 0, x_160);
lean_closure_set(x_162, 1, x_161);
lean_closure_set(x_162, 2, x_159);
x_163 = x_162;
x_164 = lean_apply_6(x_163, x_5, x_6, x_7, x_8, x_9, x_156);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = l_Lean_mkAppN(x_155, x_166);
lean_dec(x_166);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = l_Lean_mkAppN(x_155, x_168);
lean_dec(x_168);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
uint8_t x_172; 
lean_dec(x_155);
x_172 = !lean_is_exclusive(x_164);
if (x_172 == 0)
{
return x_164;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_164, 0);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_164);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_154, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_154, 1);
lean_inc(x_177);
lean_dec(x_154);
x_178 = l_Lean_Expr_isLambda(x_176);
if (x_178 == 0)
{
lean_object* x_179; size_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_array_get_size(x_3);
x_180 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_181 = x_3;
x_182 = lean_box_usize(x_180);
x_183 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
x_184 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed), 9, 3);
lean_closure_set(x_184, 0, x_182);
lean_closure_set(x_184, 1, x_183);
lean_closure_set(x_184, 2, x_181);
x_185 = x_184;
x_186 = lean_apply_6(x_185, x_5, x_6, x_7, x_8, x_9, x_177);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = l_Lean_mkAppN(x_176, x_188);
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
x_192 = l_Lean_mkAppN(x_176, x_190);
lean_dec(x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_176);
x_194 = !lean_is_exclusive(x_186);
if (x_194 == 0)
{
return x_186;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_186, 0);
x_196 = lean_ctor_get(x_186, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_186);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = l_Array_reverse___rarg(x_3);
x_199 = l_Lean_Expr_betaRev(x_176, x_198);
lean_dec(x_198);
lean_dec(x_176);
x_200 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_199, x_5, x_6, x_7, x_8, x_9, x_177);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_154);
if (x_201 == 0)
{
return x_154;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_154, 0);
x_203 = lean_ctor_get(x_154, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_154);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_get(x_6, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_37; lean_object* x_38; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_15, x_1);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_free_object(x_13);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_st_ref_get(x_6, x_16);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_2, x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_56, x_1);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_54);
x_59 = lean_st_ref_get(x_6, x_57);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_4, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_MetavarContext_getExprAssignment_x3f(x_64, x_51);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_37 = x_1;
x_38 = x_63;
goto block_50;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_67 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_66, x_2, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_6, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_take(x_4, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_68);
x_77 = l_Lean_MetavarContext_assignExpr(x_76, x_51, x_68);
lean_ctor_set(x_73, 0, x_77);
x_78 = lean_st_ref_set(x_4, x_73, x_74);
lean_dec(x_4);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_37 = x_68;
x_38 = x_79;
goto block_50;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
x_82 = lean_ctor_get(x_73, 2);
x_83 = lean_ctor_get(x_73, 3);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
lean_inc(x_68);
x_84 = l_Lean_MetavarContext_assignExpr(x_80, x_51, x_68);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_83);
x_86 = lean_st_ref_set(x_4, x_85, x_74);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_37 = x_68;
x_38 = x_87;
goto block_50;
}
}
else
{
uint8_t x_88; 
lean_dec(x_51);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_67);
if (x_88 == 0)
{
x_18 = x_67;
goto block_36;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_67, 0);
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_67);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_18 = x_91;
goto block_36;
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = lean_ctor_get(x_58, 0);
lean_inc(x_92);
lean_dec(x_58);
lean_ctor_set(x_54, 0, x_92);
x_18 = x_54;
goto block_36;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_54, 0);
x_94 = lean_ctor_get(x_54, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_54);
x_95 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_93, x_1);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_st_ref_get(x_6, x_94);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_st_ref_get(x_4, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_MetavarContext_getExprAssignment_x3f(x_101, x_51);
if (lean_obj_tag(x_102) == 0)
{
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_37 = x_1;
x_38 = x_100;
goto block_50;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_104 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_103, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_get(x_6, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_ref_take(x_4, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
lean_inc(x_105);
x_117 = l_Lean_MetavarContext_assignExpr(x_112, x_51, x_105);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 4, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
lean_ctor_set(x_118, 2, x_114);
lean_ctor_set(x_118, 3, x_115);
x_119 = lean_st_ref_set(x_4, x_118, x_111);
lean_dec(x_4);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_37 = x_105;
x_38 = x_120;
goto block_50;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_51);
lean_dec(x_4);
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_104, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_123 = x_104;
} else {
 lean_dec_ref(x_104);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
x_18 = x_124;
goto block_36;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_95, 0);
lean_inc(x_125);
lean_dec(x_95);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_94);
x_18 = x_126;
goto block_36;
}
}
}
case 3:
{
lean_object* x_127; uint64_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_129 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_130 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_131 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_132 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_133 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
lean_inc(x_127);
x_134 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_127, x_129, x_130, x_131, x_132, x_133);
lean_inc(x_6);
lean_inc(x_2);
x_135 = lean_apply_6(x_134, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set_uint64(x_138, sizeof(void*)*1, x_128);
x_139 = lean_expr_update_sort(x_138, x_136);
x_140 = lean_st_ref_get(x_6, x_137);
lean_dec(x_6);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_2, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_139);
x_145 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_143, x_1, x_139);
x_146 = lean_st_ref_set(x_2, x_145, x_144);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_dec(x_148);
lean_ctor_set(x_146, 0, x_139);
return x_146;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
uint8_t x_151; 
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_135);
if (x_151 == 0)
{
return x_135;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_135, 0);
x_153 = lean_ctor_get(x_135, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_135);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
case 4:
{
lean_object* x_155; lean_object* x_156; uint64_t x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_1, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_1, 1);
lean_inc(x_156);
x_157 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_156);
x_158 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_8, x_156, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set_uint64(x_161, sizeof(void*)*2, x_157);
x_162 = lean_expr_update_const(x_161, x_159);
x_163 = lean_st_ref_get(x_6, x_160);
lean_dec(x_6);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_take(x_2, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_162);
x_168 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_166, x_1, x_162);
x_169 = lean_st_ref_set(x_2, x_168, x_167);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
lean_ctor_set(x_169, 0, x_162);
return x_169;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_158);
if (x_174 == 0)
{
return x_158;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_158, 0);
x_176 = lean_ctor_get(x_158, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_158);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
case 5:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Lean_Expr_getAppNumArgsAux(x_1, x_178);
x_180 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_179);
x_181 = lean_mk_array(x_179, x_180);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_sub(x_179, x_182);
lean_dec(x_179);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_184 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(x_8, x_1, x_181, x_183, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_st_ref_get(x_6, x_186);
lean_dec(x_6);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_st_ref_take(x_2, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_185);
x_192 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_190, x_1, x_185);
x_193 = lean_st_ref_set(x_2, x_192, x_191);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_dec(x_195);
lean_ctor_set(x_193, 0, x_185);
return x_193;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_185);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
else
{
uint8_t x_198; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
return x_184;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_184, 0);
x_200 = lean_ctor_get(x_184, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_184);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
case 6:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint64_t x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_1, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_203);
x_206 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_203, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_204);
x_209 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_204, x_2, x_3, x_4, x_5, x_6, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_203);
lean_ctor_set(x_212, 2, x_204);
lean_ctor_set_uint64(x_212, sizeof(void*)*3, x_205);
x_213 = (uint8_t)((x_205 << 24) >> 61);
x_214 = lean_expr_update_lambda(x_212, x_213, x_207, x_210);
x_215 = lean_st_ref_get(x_6, x_211);
lean_dec(x_6);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_2, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_214);
x_220 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_218, x_1, x_214);
x_221 = lean_st_ref_set(x_2, x_220, x_219);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_dec(x_223);
lean_ctor_set(x_221, 0, x_214);
return x_221;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_214);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
else
{
uint8_t x_226; 
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_209);
if (x_226 == 0)
{
return x_209;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_209, 0);
x_228 = lean_ctor_get(x_209, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_209);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_206);
if (x_230 == 0)
{
return x_206;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_206, 0);
x_232 = lean_ctor_get(x_206, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_206);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
case 7:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint64_t x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_1, 2);
lean_inc(x_236);
x_237 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_235);
x_238 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_235, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_236);
x_241 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_236, x_2, x_3, x_4, x_5, x_6, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_236);
lean_ctor_set_uint64(x_244, sizeof(void*)*3, x_237);
x_245 = (uint8_t)((x_237 << 24) >> 61);
x_246 = lean_expr_update_forall(x_244, x_245, x_239, x_242);
x_247 = lean_st_ref_get(x_6, x_243);
lean_dec(x_6);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_st_ref_take(x_2, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_246);
x_252 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_250, x_1, x_246);
x_253 = lean_st_ref_set(x_2, x_252, x_251);
lean_dec(x_2);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_253, 0);
lean_dec(x_255);
lean_ctor_set(x_253, 0, x_246);
return x_253;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_246);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
else
{
uint8_t x_258; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_241);
if (x_258 == 0)
{
return x_241;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_241, 0);
x_260 = lean_ctor_get(x_241, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_241);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_238);
if (x_262 == 0)
{
return x_238;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_238, 0);
x_264 = lean_ctor_get(x_238, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_238);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
case 8:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint64_t x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_1, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_1, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_1, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_1, 3);
lean_inc(x_269);
x_270 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_267);
x_271 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_267, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_268);
x_274 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_268, x_2, x_3, x_4, x_5, x_6, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_269);
x_277 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_269, x_2, x_3, x_4, x_5, x_6, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_280, 0, x_266);
lean_ctor_set(x_280, 1, x_267);
lean_ctor_set(x_280, 2, x_268);
lean_ctor_set(x_280, 3, x_269);
lean_ctor_set_uint64(x_280, sizeof(void*)*4, x_270);
x_281 = lean_expr_update_let(x_280, x_272, x_275, x_278);
x_282 = lean_st_ref_get(x_6, x_279);
lean_dec(x_6);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_st_ref_take(x_2, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_281);
x_287 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_285, x_1, x_281);
x_288 = lean_st_ref_set(x_2, x_287, x_286);
lean_dec(x_2);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_288, 0);
lean_dec(x_290);
lean_ctor_set(x_288, 0, x_281);
return x_288;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
else
{
uint8_t x_293; 
lean_dec(x_275);
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_277);
if (x_293 == 0)
{
return x_277;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_277, 0);
x_295 = lean_ctor_get(x_277, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_277);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_274);
if (x_297 == 0)
{
return x_274;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_274, 0);
x_299 = lean_ctor_get(x_274, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_274);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_271);
if (x_301 == 0)
{
return x_271;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_271, 0);
x_303 = lean_ctor_get(x_271, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_271);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
case 10:
{
lean_object* x_305; lean_object* x_306; uint64_t x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_1, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_1, 1);
lean_inc(x_306);
x_307 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_306);
x_308 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_306, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_311, 0, x_305);
lean_ctor_set(x_311, 1, x_306);
lean_ctor_set_uint64(x_311, sizeof(void*)*2, x_307);
x_312 = lean_expr_update_mdata(x_311, x_309);
x_313 = lean_st_ref_get(x_6, x_310);
lean_dec(x_6);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_st_ref_take(x_2, x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_312);
x_318 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_316, x_1, x_312);
x_319 = lean_st_ref_set(x_2, x_318, x_317);
lean_dec(x_2);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_319, 0);
lean_dec(x_321);
lean_ctor_set(x_319, 0, x_312);
return x_319;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_312);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
else
{
uint8_t x_324; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_308);
if (x_324 == 0)
{
return x_308;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_308, 0);
x_326 = lean_ctor_get(x_308, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_308);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
case 11:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint64_t x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_1, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_1, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_1, 2);
lean_inc(x_330);
x_331 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_330);
x_332 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_330, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_335, 0, x_328);
lean_ctor_set(x_335, 1, x_329);
lean_ctor_set(x_335, 2, x_330);
lean_ctor_set_uint64(x_335, sizeof(void*)*3, x_331);
x_336 = lean_expr_update_proj(x_335, x_333);
x_337 = lean_st_ref_get(x_6, x_334);
lean_dec(x_6);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = lean_st_ref_take(x_2, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
lean_inc(x_336);
x_342 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_340, x_1, x_336);
x_343 = lean_st_ref_set(x_2, x_342, x_341);
lean_dec(x_2);
x_344 = !lean_is_exclusive(x_343);
if (x_344 == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_343, 0);
lean_dec(x_345);
lean_ctor_set(x_343, 0, x_336);
return x_343;
}
else
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_336);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
else
{
uint8_t x_348; 
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_332);
if (x_348 == 0)
{
return x_332;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_332, 0);
x_350 = lean_ctor_get(x_332, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_332);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
default: 
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_352 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_st_ref_take(x_2, x_353);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc_n(x_1, 2);
x_357 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_355, x_1, x_1);
x_358 = lean_st_ref_set(x_2, x_357, x_356);
lean_dec(x_2);
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_358, 0);
lean_dec(x_360);
lean_ctor_set(x_358, 0, x_1);
return x_358;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_dec(x_358);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
}
else
{
lean_object* x_363; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_363 = lean_ctor_get(x_17, 0);
lean_inc(x_363);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_363);
return x_13;
}
block_36:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_6, x_20);
lean_dec(x_6);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_19);
x_26 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_24, x_1, x_19);
x_27 = lean_st_ref_set(x_2, x_26, x_25);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_50:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_st_ref_get(x_6, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_2, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_37);
lean_inc(x_1);
x_44 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_42, x_1, x_37);
x_45 = lean_st_ref_set(x_2, x_44, x_43);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_37);
x_18 = x_45;
goto block_36;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
x_18 = x_49;
goto block_36;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_385; lean_object* x_386; 
x_364 = lean_ctor_get(x_13, 0);
x_365 = lean_ctor_get(x_13, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_13);
x_366 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_364, x_1);
lean_dec(x_364);
if (lean_obj_tag(x_366) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_398 = lean_ctor_get(x_1, 0);
lean_inc(x_398);
x_399 = lean_st_ref_get(x_6, x_365);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = lean_st_ref_get(x_2, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_402, x_1);
lean_dec(x_402);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_404);
x_406 = lean_st_ref_get(x_6, x_403);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
x_408 = lean_st_ref_get(x_4, x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
lean_dec(x_409);
x_412 = l_Lean_MetavarContext_getExprAssignment_x3f(x_411, x_398);
if (lean_obj_tag(x_412) == 0)
{
lean_dec(x_398);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_385 = x_1;
x_386 = x_410;
goto block_397;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec(x_412);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_414 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_413, x_2, x_3, x_4, x_5, x_6, x_410);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_st_ref_get(x_6, x_416);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_st_ref_take(x_4, x_418);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_420, 2);
lean_inc(x_424);
x_425 = lean_ctor_get(x_420, 3);
lean_inc(x_425);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_426 = x_420;
} else {
 lean_dec_ref(x_420);
 x_426 = lean_box(0);
}
lean_inc(x_415);
x_427 = l_Lean_MetavarContext_assignExpr(x_422, x_398, x_415);
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(0, 4, 0);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_423);
lean_ctor_set(x_428, 2, x_424);
lean_ctor_set(x_428, 3, x_425);
x_429 = lean_st_ref_set(x_4, x_428, x_421);
lean_dec(x_4);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec(x_429);
x_385 = x_415;
x_386 = x_430;
goto block_397;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_398);
lean_dec(x_4);
x_431 = lean_ctor_get(x_414, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_414, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_433 = x_414;
} else {
 lean_dec_ref(x_414);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
x_367 = x_434;
goto block_384;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_398);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_435 = lean_ctor_get(x_405, 0);
lean_inc(x_435);
lean_dec(x_405);
if (lean_is_scalar(x_404)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_404;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_403);
x_367 = x_436;
goto block_384;
}
}
case 3:
{
lean_object* x_437; uint64_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_437 = lean_ctor_get(x_1, 0);
lean_inc(x_437);
x_438 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_439 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed), 9, 0);
x_440 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed), 10, 0);
x_441 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed), 10, 0);
x_442 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed), 9, 0);
x_443 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed), 7, 0);
lean_inc(x_437);
x_444 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_437, x_439, x_440, x_441, x_442, x_443);
lean_inc(x_6);
lean_inc(x_2);
x_445 = lean_apply_6(x_444, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_448, 0, x_437);
lean_ctor_set_uint64(x_448, sizeof(void*)*1, x_438);
x_449 = lean_expr_update_sort(x_448, x_446);
x_450 = lean_st_ref_get(x_6, x_447);
lean_dec(x_6);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_452 = lean_st_ref_take(x_2, x_451);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
lean_inc(x_449);
x_455 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_453, x_1, x_449);
x_456 = lean_st_ref_set(x_2, x_455, x_454);
lean_dec(x_2);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_449);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_437);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_460 = lean_ctor_get(x_445, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_445, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_462 = x_445;
} else {
 lean_dec_ref(x_445);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
}
case 4:
{
lean_object* x_464; lean_object* x_465; uint64_t x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_1, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_1, 1);
lean_inc(x_465);
x_466 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_465);
x_467 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_8, x_465, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_470, 0, x_464);
lean_ctor_set(x_470, 1, x_465);
lean_ctor_set_uint64(x_470, sizeof(void*)*2, x_466);
x_471 = lean_expr_update_const(x_470, x_468);
x_472 = lean_st_ref_get(x_6, x_469);
lean_dec(x_6);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_474 = lean_st_ref_take(x_2, x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
lean_inc(x_471);
x_477 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_475, x_1, x_471);
x_478 = lean_st_ref_set(x_2, x_477, x_476);
lean_dec(x_2);
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_480 = x_478;
} else {
 lean_dec_ref(x_478);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_471);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_482 = lean_ctor_get(x_467, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_467, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_484 = x_467;
} else {
 lean_dec_ref(x_467);
 x_484 = lean_box(0);
}
if (lean_is_scalar(x_484)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_484;
}
lean_ctor_set(x_485, 0, x_482);
lean_ctor_set(x_485, 1, x_483);
return x_485;
}
}
case 5:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_486 = lean_unsigned_to_nat(0u);
x_487 = l_Lean_Expr_getAppNumArgsAux(x_1, x_486);
x_488 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_487);
x_489 = lean_mk_array(x_487, x_488);
x_490 = lean_unsigned_to_nat(1u);
x_491 = lean_nat_sub(x_487, x_490);
lean_dec(x_487);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_492 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(x_8, x_1, x_489, x_491, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_495 = lean_st_ref_get(x_6, x_494);
lean_dec(x_6);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
lean_dec(x_495);
x_497 = lean_st_ref_take(x_2, x_496);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
lean_inc(x_493);
x_500 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_498, x_1, x_493);
x_501 = lean_st_ref_set(x_2, x_500, x_499);
lean_dec(x_2);
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_503 = x_501;
} else {
 lean_dec_ref(x_501);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_493);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_505 = lean_ctor_get(x_492, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_492, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_507 = x_492;
} else {
 lean_dec_ref(x_492);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
case 6:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; uint64_t x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_1, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_1, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_1, 2);
lean_inc(x_511);
x_512 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_510);
x_513 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_510, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_511);
x_516 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_511, x_2, x_3, x_4, x_5, x_6, x_515);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_519, 0, x_509);
lean_ctor_set(x_519, 1, x_510);
lean_ctor_set(x_519, 2, x_511);
lean_ctor_set_uint64(x_519, sizeof(void*)*3, x_512);
x_520 = (uint8_t)((x_512 << 24) >> 61);
x_521 = lean_expr_update_lambda(x_519, x_520, x_514, x_517);
x_522 = lean_st_ref_get(x_6, x_518);
lean_dec(x_6);
x_523 = lean_ctor_get(x_522, 1);
lean_inc(x_523);
lean_dec(x_522);
x_524 = lean_st_ref_take(x_2, x_523);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
lean_inc(x_521);
x_527 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_525, x_1, x_521);
x_528 = lean_st_ref_set(x_2, x_527, x_526);
lean_dec(x_2);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_530 = x_528;
} else {
 lean_dec_ref(x_528);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_521);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_514);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_532 = lean_ctor_get(x_516, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_516, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_534 = x_516;
} else {
 lean_dec_ref(x_516);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_536 = lean_ctor_get(x_513, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_513, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_538 = x_513;
} else {
 lean_dec_ref(x_513);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
case 7:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint64_t x_543; lean_object* x_544; 
x_540 = lean_ctor_get(x_1, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_1, 1);
lean_inc(x_541);
x_542 = lean_ctor_get(x_1, 2);
lean_inc(x_542);
x_543 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_541);
x_544 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_541, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_542);
x_547 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_542, x_2, x_3, x_4, x_5, x_6, x_546);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_550 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_550, 0, x_540);
lean_ctor_set(x_550, 1, x_541);
lean_ctor_set(x_550, 2, x_542);
lean_ctor_set_uint64(x_550, sizeof(void*)*3, x_543);
x_551 = (uint8_t)((x_543 << 24) >> 61);
x_552 = lean_expr_update_forall(x_550, x_551, x_545, x_548);
x_553 = lean_st_ref_get(x_6, x_549);
lean_dec(x_6);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
lean_dec(x_553);
x_555 = lean_st_ref_take(x_2, x_554);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
lean_inc(x_552);
x_558 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_556, x_1, x_552);
x_559 = lean_st_ref_set(x_2, x_558, x_557);
lean_dec(x_2);
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_561 = x_559;
} else {
 lean_dec_ref(x_559);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_552);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_545);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_563 = lean_ctor_get(x_547, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_547, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_565 = x_547;
} else {
 lean_dec_ref(x_547);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(1, 2, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_563);
lean_ctor_set(x_566, 1, x_564);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_567 = lean_ctor_get(x_544, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_544, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_569 = x_544;
} else {
 lean_dec_ref(x_544);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
case 8:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint64_t x_575; lean_object* x_576; 
x_571 = lean_ctor_get(x_1, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_1, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_1, 2);
lean_inc(x_573);
x_574 = lean_ctor_get(x_1, 3);
lean_inc(x_574);
x_575 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_572);
x_576 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_572, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_573);
x_579 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_573, x_2, x_3, x_4, x_5, x_6, x_578);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_574);
x_582 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_574, x_2, x_3, x_4, x_5, x_6, x_581);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_585, 0, x_571);
lean_ctor_set(x_585, 1, x_572);
lean_ctor_set(x_585, 2, x_573);
lean_ctor_set(x_585, 3, x_574);
lean_ctor_set_uint64(x_585, sizeof(void*)*4, x_575);
x_586 = lean_expr_update_let(x_585, x_577, x_580, x_583);
x_587 = lean_st_ref_get(x_6, x_584);
lean_dec(x_6);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
lean_dec(x_587);
x_589 = lean_st_ref_take(x_2, x_588);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
lean_inc(x_586);
x_592 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_590, x_1, x_586);
x_593 = lean_st_ref_set(x_2, x_592, x_591);
lean_dec(x_2);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_586);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_580);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_597 = lean_ctor_get(x_582, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_582, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_599 = x_582;
} else {
 lean_dec_ref(x_582);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_601 = lean_ctor_get(x_579, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_579, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_603 = x_579;
} else {
 lean_dec_ref(x_579);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_605 = lean_ctor_get(x_576, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_576, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_607 = x_576;
} else {
 lean_dec_ref(x_576);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
return x_608;
}
}
case 10:
{
lean_object* x_609; lean_object* x_610; uint64_t x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_1, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_1, 1);
lean_inc(x_610);
x_611 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_610);
x_612 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_610, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_615, 0, x_609);
lean_ctor_set(x_615, 1, x_610);
lean_ctor_set_uint64(x_615, sizeof(void*)*2, x_611);
x_616 = lean_expr_update_mdata(x_615, x_613);
x_617 = lean_st_ref_get(x_6, x_614);
lean_dec(x_6);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_619 = lean_st_ref_take(x_2, x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
lean_inc(x_616);
x_622 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_620, x_1, x_616);
x_623 = lean_st_ref_set(x_2, x_622, x_621);
lean_dec(x_2);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_625 = x_623;
} else {
 lean_dec_ref(x_623);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_616);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_627 = lean_ctor_get(x_612, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_612, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_629 = x_612;
} else {
 lean_dec_ref(x_612);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
}
}
case 11:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; uint64_t x_634; lean_object* x_635; 
x_631 = lean_ctor_get(x_1, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_1, 1);
lean_inc(x_632);
x_633 = lean_ctor_get(x_1, 2);
lean_inc(x_633);
x_634 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_633);
x_635 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_633, x_2, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_638, 0, x_631);
lean_ctor_set(x_638, 1, x_632);
lean_ctor_set(x_638, 2, x_633);
lean_ctor_set_uint64(x_638, sizeof(void*)*3, x_634);
x_639 = lean_expr_update_proj(x_638, x_636);
x_640 = lean_st_ref_get(x_6, x_637);
lean_dec(x_6);
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
lean_dec(x_640);
x_642 = lean_st_ref_take(x_2, x_641);
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
lean_dec(x_642);
lean_inc(x_639);
x_645 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_643, x_1, x_639);
x_646 = lean_st_ref_set(x_2, x_645, x_644);
lean_dec(x_2);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_648 = x_646;
} else {
 lean_dec_ref(x_646);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_639);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_650 = lean_ctor_get(x_635, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_635, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_652 = x_635;
} else {
 lean_dec_ref(x_635);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
default: 
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_654 = lean_st_ref_get(x_6, x_365);
lean_dec(x_6);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
lean_dec(x_654);
x_656 = lean_st_ref_take(x_2, x_655);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
lean_inc_n(x_1, 2);
x_659 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_657, x_1, x_1);
x_660 = lean_st_ref_set(x_2, x_659, x_658);
lean_dec(x_2);
x_661 = lean_ctor_get(x_660, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_662 = x_660;
} else {
 lean_dec_ref(x_660);
 x_662 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_662;
}
lean_ctor_set(x_663, 0, x_1);
lean_ctor_set(x_663, 1, x_661);
return x_663;
}
}
}
else
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_664 = lean_ctor_get(x_366, 0);
lean_inc(x_664);
lean_dec(x_366);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_365);
return x_665;
}
block_384:
{
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_st_ref_get(x_6, x_369);
lean_dec(x_6);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = lean_st_ref_take(x_2, x_371);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_368);
x_375 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_373, x_1, x_368);
x_376 = lean_st_ref_set(x_2, x_375, x_374);
lean_dec(x_2);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_368);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_380 = lean_ctor_get(x_367, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_367, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_382 = x_367;
} else {
 lean_dec_ref(x_367);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
block_397:
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_387 = lean_st_ref_get(x_6, x_386);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_st_ref_take(x_2, x_388);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
lean_inc(x_385);
lean_inc(x_1);
x_392 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_390, x_1, x_385);
x_393 = lean_st_ref_set(x_2, x_392, x_391);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_385);
lean_ctor_set(x_396, 1, x_394);
x_367 = x_396;
goto block_384;
}
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_11);
x_13 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; lean_object* x_12; 
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; lean_object* x_12; 
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLocalDeclMVars_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Meta_instantiateMVars(x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 3, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_27 = l_Lean_Meta_instantiateMVars(x_25, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_26);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Meta_instantiateMVars(x_41, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_instantiateMVars(x_42, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_1, 4, x_48);
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_1, 4, x_49);
lean_ctor_set(x_1, 3, x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_44);
lean_free_object(x_1);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_1);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
return x_43;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_43, 0);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 1);
x_62 = lean_ctor_get(x_1, 2);
x_63 = lean_ctor_get(x_1, 3);
x_64 = lean_ctor_get(x_1, 4);
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Meta_instantiateMVars(x_63, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_instantiateMVars(x_64, x_2, x_3, x_4, x_5, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_67);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*5, x_65);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_81 = x_66;
} else {
 lean_dec_ref(x_66);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
lean_object* l_Lean_Meta_liftMkBindingM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_5(x_3, x_9, x_10, x_11, x_12, x_8);
return x_13;
}
}
}
lean_object* l_Lean_Meta_liftMkBindingM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_liftMkBindingM_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_liftMkBindingM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create binder due to failure when reverting variable dependencies");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_liftMkBindingM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_liftMkBindingM___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_liftMkBindingM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_liftMkBindingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_apply_2(x_1, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_st_ref_take(x_5, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_25, 2);
lean_dec(x_28);
lean_ctor_set(x_25, 2, x_23);
x_29 = lean_st_ref_set(x_5, x_25, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Meta_setMCtx(x_31, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_21);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
x_39 = lean_ctor_get(x_25, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_st_ref_set(x_5, x_40, x_26);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
lean_dec(x_22);
x_44 = l_Lean_Meta_setMCtx(x_43, x_2, x_3, x_4, x_5, x_42);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_dec(x_20);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = l_Lean_Meta_setMCtx(x_49, x_2, x_3, x_4, x_5, x_16);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_st_ref_take(x_5, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_54, 2);
lean_dec(x_57);
lean_ctor_set(x_54, 2, x_52);
x_58 = lean_st_ref_set(x_5, x_54, x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_liftMkBindingM___rarg___closed__3;
x_61 = l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(x_60, x_2, x_3, x_4, x_5, x_59);
lean_dec(x_2);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
x_64 = lean_ctor_get(x_54, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_st_ref_set(x_5, x_65, x_55);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Meta_liftMkBindingM___rarg___closed__3;
x_69 = l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(x_68, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_2);
return x_69;
}
}
}
}
lean_object* l_Lean_Meta_liftMkBindingM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_liftMkBindingM___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_liftMkBindingM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_liftMkBindingM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_3);
x_12 = lean_box(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_mkForall___boxed), 6, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_Meta_liftMkBindingM___rarg(x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_3);
x_12 = lean_box(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_MetavarContext_mkLambda___boxed), 6, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_Meta_liftMkBindingM___rarg(x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_mkLetFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = 1;
x_10 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkLetFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_mkArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_mkArrow___closed__2;
x_9 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_8, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = 0;
x_13 = l_Lean_mkForall(x_11, x_12, x_1, x_2);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = 0;
x_17 = l_Lean_mkForall(x_14, x_16, x_1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l_Lean_Meta_mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_elimMVarDeps(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_MetavarContext_elimMVarDeps___boxed), 5, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_Meta_liftMkBindingM___rarg(x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
lean_object* l_Lean_Meta_elimMVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_elimMVarDeps(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l_Lean_Meta_withConfig___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
x_12 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_16 = lean_apply_1(x_1, x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_apply_7(x_3, lean_box(0), x_2, x_17, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
lean_object* l_Lean_Meta_withConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_withConfig___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withConfig___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withTrackingZeta___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 7, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get_uint8(x_9, 0);
x_14 = lean_ctor_get_uint8(x_9, 1);
x_15 = lean_ctor_get_uint8(x_9, 2);
x_16 = lean_ctor_get_uint8(x_9, 3);
x_17 = lean_ctor_get_uint8(x_9, 4);
x_18 = lean_ctor_get_uint8(x_9, 5);
x_19 = lean_ctor_get_uint8(x_9, 6);
x_20 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_22, 0, x_13);
lean_ctor_set_uint8(x_22, 1, x_14);
lean_ctor_set_uint8(x_22, 2, x_15);
lean_ctor_set_uint8(x_22, 3, x_16);
lean_ctor_set_uint8(x_22, 4, x_17);
lean_ctor_set_uint8(x_22, 5, x_18);
lean_ctor_set_uint8(x_22, 6, x_19);
lean_ctor_set_uint8(x_22, 7, x_21);
lean_ctor_set_uint8(x_22, 8, x_20);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_ctor_get_uint8(x_24, 0);
x_28 = lean_ctor_get_uint8(x_24, 1);
x_29 = lean_ctor_get_uint8(x_24, 2);
x_30 = lean_ctor_get_uint8(x_24, 3);
x_31 = lean_ctor_get_uint8(x_24, 4);
x_32 = lean_ctor_get_uint8(x_24, 5);
x_33 = lean_ctor_get_uint8(x_24, 6);
x_34 = lean_ctor_get_uint8(x_24, 8);
if (lean_is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean_dec_ref(x_24);
 x_35 = lean_box(0);
}
x_36 = 1;
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 0, 9);
} else {
 x_37 = x_35;
}
lean_ctor_set_uint8(x_37, 0, x_27);
lean_ctor_set_uint8(x_37, 1, x_28);
lean_ctor_set_uint8(x_37, 2, x_29);
lean_ctor_set_uint8(x_37, 3, x_30);
lean_ctor_set_uint8(x_37, 4, x_31);
lean_ctor_set_uint8(x_37, 5, x_32);
lean_ctor_set_uint8(x_37, 6, x_33);
lean_ctor_set_uint8(x_37, 7, x_36);
lean_ctor_set_uint8(x_37, 8, x_34);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
x_39 = lean_apply_7(x_2, lean_box(0), x_1, x_38, x_4, x_5, x_6, x_7);
return x_39;
}
}
}
lean_object* l_Lean_Meta_withTrackingZeta___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withTrackingZeta___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withTrackingZeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withTrackingZeta___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_ctor_set_uint8(x_10, 5, x_1);
x_12 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get_uint8(x_10, 0);
x_22 = lean_ctor_get_uint8(x_10, 1);
x_23 = lean_ctor_get_uint8(x_10, 2);
x_24 = lean_ctor_get_uint8(x_10, 3);
x_25 = lean_ctor_get_uint8(x_10, 4);
x_26 = lean_ctor_get_uint8(x_10, 6);
x_27 = lean_ctor_get_uint8(x_10, 7);
x_28 = lean_ctor_get_uint8(x_10, 8);
lean_dec(x_10);
x_29 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_29, 0, x_21);
lean_ctor_set_uint8(x_29, 1, x_22);
lean_ctor_set_uint8(x_29, 2, x_23);
lean_ctor_set_uint8(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, 4, x_25);
lean_ctor_set_uint8(x_29, 5, x_1);
lean_ctor_set_uint8(x_29, 6, x_26);
lean_ctor_set_uint8(x_29, 7, x_27);
lean_ctor_set_uint8(x_29, 8, x_28);
lean_ctor_set(x_4, 0, x_29);
x_30 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_42 = lean_ctor_get_uint8(x_39, 0);
x_43 = lean_ctor_get_uint8(x_39, 1);
x_44 = lean_ctor_get_uint8(x_39, 2);
x_45 = lean_ctor_get_uint8(x_39, 3);
x_46 = lean_ctor_get_uint8(x_39, 4);
x_47 = lean_ctor_get_uint8(x_39, 6);
x_48 = lean_ctor_get_uint8(x_39, 7);
x_49 = lean_ctor_get_uint8(x_39, 8);
if (lean_is_exclusive(x_39)) {
 x_50 = x_39;
} else {
 lean_dec_ref(x_39);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 0, 9);
} else {
 x_51 = x_50;
}
lean_ctor_set_uint8(x_51, 0, x_42);
lean_ctor_set_uint8(x_51, 1, x_43);
lean_ctor_set_uint8(x_51, 2, x_44);
lean_ctor_set_uint8(x_51, 3, x_45);
lean_ctor_set_uint8(x_51, 4, x_46);
lean_ctor_set_uint8(x_51, 5, x_1);
lean_ctor_set_uint8(x_51, 6, x_47);
lean_ctor_set_uint8(x_51, 7, x_48);
lean_ctor_set_uint8(x_51, 8, x_49);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_41);
x_53 = lean_apply_7(x_3, lean_box(0), x_2, x_52, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
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
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
lean_object* l_Lean_Meta_withTransparency___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withTransparency___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_withTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withTransparency___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_withTransparency___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_withTransparency___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_withDefault___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_30, 0, x_21);
lean_ctor_set_uint8(x_30, 1, x_22);
lean_ctor_set_uint8(x_30, 2, x_23);
lean_ctor_set_uint8(x_30, 3, x_24);
lean_ctor_set_uint8(x_30, 4, x_25);
lean_ctor_set_uint8(x_30, 5, x_29);
lean_ctor_set_uint8(x_30, 6, x_26);
lean_ctor_set_uint8(x_30, 7, x_27);
lean_ctor_set_uint8(x_30, 8, x_28);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_43 = lean_ctor_get_uint8(x_40, 0);
x_44 = lean_ctor_get_uint8(x_40, 1);
x_45 = lean_ctor_get_uint8(x_40, 2);
x_46 = lean_ctor_get_uint8(x_40, 3);
x_47 = lean_ctor_get_uint8(x_40, 4);
x_48 = lean_ctor_get_uint8(x_40, 6);
x_49 = lean_ctor_get_uint8(x_40, 7);
x_50 = lean_ctor_get_uint8(x_40, 8);
if (lean_is_exclusive(x_40)) {
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = 1;
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 0, 9);
} else {
 x_53 = x_51;
}
lean_ctor_set_uint8(x_53, 0, x_43);
lean_ctor_set_uint8(x_53, 1, x_44);
lean_ctor_set_uint8(x_53, 2, x_45);
lean_ctor_set_uint8(x_53, 3, x_46);
lean_ctor_set_uint8(x_53, 4, x_47);
lean_ctor_set_uint8(x_53, 5, x_52);
lean_ctor_set_uint8(x_53, 6, x_48);
lean_ctor_set_uint8(x_53, 7, x_49);
lean_ctor_set_uint8(x_53, 8, x_50);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_54, 2, x_42);
x_55 = lean_apply_7(x_2, lean_box(0), x_1, x_54, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
lean_object* l_Lean_Meta_withDefault___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withDefault___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withDefault___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withReducible___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_29 = 2;
x_30 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_30, 0, x_21);
lean_ctor_set_uint8(x_30, 1, x_22);
lean_ctor_set_uint8(x_30, 2, x_23);
lean_ctor_set_uint8(x_30, 3, x_24);
lean_ctor_set_uint8(x_30, 4, x_25);
lean_ctor_set_uint8(x_30, 5, x_29);
lean_ctor_set_uint8(x_30, 6, x_26);
lean_ctor_set_uint8(x_30, 7, x_27);
lean_ctor_set_uint8(x_30, 8, x_28);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_43 = lean_ctor_get_uint8(x_40, 0);
x_44 = lean_ctor_get_uint8(x_40, 1);
x_45 = lean_ctor_get_uint8(x_40, 2);
x_46 = lean_ctor_get_uint8(x_40, 3);
x_47 = lean_ctor_get_uint8(x_40, 4);
x_48 = lean_ctor_get_uint8(x_40, 6);
x_49 = lean_ctor_get_uint8(x_40, 7);
x_50 = lean_ctor_get_uint8(x_40, 8);
if (lean_is_exclusive(x_40)) {
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = 2;
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 0, 9);
} else {
 x_53 = x_51;
}
lean_ctor_set_uint8(x_53, 0, x_43);
lean_ctor_set_uint8(x_53, 1, x_44);
lean_ctor_set_uint8(x_53, 2, x_45);
lean_ctor_set_uint8(x_53, 3, x_46);
lean_ctor_set_uint8(x_53, 4, x_47);
lean_ctor_set_uint8(x_53, 5, x_52);
lean_ctor_set_uint8(x_53, 6, x_48);
lean_ctor_set_uint8(x_53, 7, x_49);
lean_ctor_set_uint8(x_53, 8, x_50);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_54, 2, x_42);
x_55 = lean_apply_7(x_2, lean_box(0), x_1, x_54, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
lean_object* l_Lean_Meta_withReducible___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withReducible___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withReducible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withReducible___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withReducibleAndInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 3;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_30, 0, x_21);
lean_ctor_set_uint8(x_30, 1, x_22);
lean_ctor_set_uint8(x_30, 2, x_23);
lean_ctor_set_uint8(x_30, 3, x_24);
lean_ctor_set_uint8(x_30, 4, x_25);
lean_ctor_set_uint8(x_30, 5, x_29);
lean_ctor_set_uint8(x_30, 6, x_26);
lean_ctor_set_uint8(x_30, 7, x_27);
lean_ctor_set_uint8(x_30, 8, x_28);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_43 = lean_ctor_get_uint8(x_40, 0);
x_44 = lean_ctor_get_uint8(x_40, 1);
x_45 = lean_ctor_get_uint8(x_40, 2);
x_46 = lean_ctor_get_uint8(x_40, 3);
x_47 = lean_ctor_get_uint8(x_40, 4);
x_48 = lean_ctor_get_uint8(x_40, 6);
x_49 = lean_ctor_get_uint8(x_40, 7);
x_50 = lean_ctor_get_uint8(x_40, 8);
if (lean_is_exclusive(x_40)) {
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = 3;
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 0, 9);
} else {
 x_53 = x_51;
}
lean_ctor_set_uint8(x_53, 0, x_43);
lean_ctor_set_uint8(x_53, 1, x_44);
lean_ctor_set_uint8(x_53, 2, x_45);
lean_ctor_set_uint8(x_53, 3, x_46);
lean_ctor_set_uint8(x_53, 4, x_47);
lean_ctor_set_uint8(x_53, 5, x_52);
lean_ctor_set_uint8(x_53, 6, x_48);
lean_ctor_set_uint8(x_53, 7, x_49);
lean_ctor_set_uint8(x_53, 8, x_50);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_54, 2, x_42);
x_55 = lean_apply_7(x_2, lean_box(0), x_1, x_54, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
lean_object* l_Lean_Meta_withReducibleAndInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withReducibleAndInstances___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withReducibleAndInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withReducibleAndInstances___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint8(x_10, 5);
x_13 = l_Lean_Meta_TransparencyMode_lt(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; 
lean_ctor_set_uint8(x_10, 5, x_1);
x_15 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get_uint8(x_10, 0);
x_17 = lean_ctor_get_uint8(x_10, 1);
x_18 = lean_ctor_get_uint8(x_10, 2);
x_19 = lean_ctor_get_uint8(x_10, 3);
x_20 = lean_ctor_get_uint8(x_10, 4);
x_21 = lean_ctor_get_uint8(x_10, 5);
x_22 = lean_ctor_get_uint8(x_10, 6);
x_23 = lean_ctor_get_uint8(x_10, 7);
x_24 = lean_ctor_get_uint8(x_10, 8);
lean_dec(x_10);
x_25 = l_Lean_Meta_TransparencyMode_lt(x_21, x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_26, 0, x_16);
lean_ctor_set_uint8(x_26, 1, x_17);
lean_ctor_set_uint8(x_26, 2, x_18);
lean_ctor_set_uint8(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, 4, x_20);
lean_ctor_set_uint8(x_26, 5, x_21);
lean_ctor_set_uint8(x_26, 6, x_22);
lean_ctor_set_uint8(x_26, 7, x_23);
lean_ctor_set_uint8(x_26, 8, x_24);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_28, 0, x_16);
lean_ctor_set_uint8(x_28, 1, x_17);
lean_ctor_set_uint8(x_28, 2, x_18);
lean_ctor_set_uint8(x_28, 3, x_19);
lean_ctor_set_uint8(x_28, 4, x_20);
lean_ctor_set_uint8(x_28, 5, x_1);
lean_ctor_set_uint8(x_28, 6, x_22);
lean_ctor_set_uint8(x_28, 7, x_23);
lean_ctor_set_uint8(x_28, 8, x_24);
lean_ctor_set(x_4, 0, x_28);
x_29 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_33 = lean_ctor_get_uint8(x_30, 0);
x_34 = lean_ctor_get_uint8(x_30, 1);
x_35 = lean_ctor_get_uint8(x_30, 2);
x_36 = lean_ctor_get_uint8(x_30, 3);
x_37 = lean_ctor_get_uint8(x_30, 4);
x_38 = lean_ctor_get_uint8(x_30, 5);
x_39 = lean_ctor_get_uint8(x_30, 6);
x_40 = lean_ctor_get_uint8(x_30, 7);
x_41 = lean_ctor_get_uint8(x_30, 8);
if (lean_is_exclusive(x_30)) {
 x_42 = x_30;
} else {
 lean_dec_ref(x_30);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Meta_TransparencyMode_lt(x_38, x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 0, 9);
} else {
 x_44 = x_42;
}
lean_ctor_set_uint8(x_44, 0, x_33);
lean_ctor_set_uint8(x_44, 1, x_34);
lean_ctor_set_uint8(x_44, 2, x_35);
lean_ctor_set_uint8(x_44, 3, x_36);
lean_ctor_set_uint8(x_44, 4, x_37);
lean_ctor_set_uint8(x_44, 5, x_38);
lean_ctor_set_uint8(x_44, 6, x_39);
lean_ctor_set_uint8(x_44, 7, x_40);
lean_ctor_set_uint8(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set(x_45, 2, x_32);
x_46 = lean_apply_7(x_3, lean_box(0), x_2, x_45, x_5, x_6, x_7, x_8);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 0, 9);
} else {
 x_47 = x_42;
}
lean_ctor_set_uint8(x_47, 0, x_33);
lean_ctor_set_uint8(x_47, 1, x_34);
lean_ctor_set_uint8(x_47, 2, x_35);
lean_ctor_set_uint8(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, 4, x_37);
lean_ctor_set_uint8(x_47, 5, x_1);
lean_ctor_set_uint8(x_47, 6, x_39);
lean_ctor_set_uint8(x_47, 7, x_40);
lean_ctor_set_uint8(x_47, 8, x_41);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_31);
lean_ctor_set(x_48, 2, x_32);
x_49 = lean_apply_7(x_3, lean_box(0), x_2, x_48, x_5, x_6, x_7, x_8);
return x_49;
}
}
}
}
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_withAtLeastTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withAtLeastTransparency___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_withAtLeastTransparency___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_13 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_12);
x_23 = lean_st_ref_set(x_3, x_19, x_20);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_20);
lean_dec(x_3);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_st_ref_get(x_5, x_37);
lean_dec(x_5);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_take(x_3, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_12);
x_45 = lean_st_ref_set(x_3, x_41, x_42);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_36);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 2);
x_52 = lean_ctor_get(x_41, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_3, x_53, x_42);
lean_dec(x_3);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_4);
x_14 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
lean_ctor_set(x_20, 1, x_13);
x_24 = lean_st_ref_set(x_4, x_20, x_21);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 2);
x_31 = lean_ctor_get(x_20, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_4, x_32, x_21);
lean_dec(x_4);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_st_ref_get(x_6, x_38);
lean_dec(x_6);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_4, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
lean_ctor_set(x_42, 1, x_13);
x_46 = lean_st_ref_set(x_4, x_42, x_43);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_37);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 2);
x_53 = lean_ctor_get(x_42, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_4, x_54, x_43);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
lean_object* l_Lean_Meta_savingCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_savingCache___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_savingCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_savingCache___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getTheoremInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_getTheoremInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getTheoremInfo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_get_reducibility_status(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_get_reducibility_status(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_name(x_1);
x_11 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_10, x_2, x_3, x_4, x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = l_Lean_ConstantInfo_name(x_1);
x_28 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_27, x_2, x_3, x_4, x_5, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
default: 
{
uint8_t x_43; 
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_7, 0);
lean_dec(x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_7, 0, x_45);
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
switch (lean_obj_tag(x_8)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_apply_2(x_2, x_8, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_8);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
x_8 = l_Lean_mkConst(x_1, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_KernelException_toMessageData___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getTheoremInfo(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_environment_find(x_10, x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4___boxed), 7, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1;
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2;
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3;
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_match__1___rarg(x_11, x_13, x_14, x_15, x_12);
x_17 = lean_apply_5(x_16, x_2, x_3, x_4, x_5, x_9);
return x_17;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_is_class(x_11, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_box(2);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = lean_is_class(x_34, x_1);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(x_1, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
x_44 = lean_box(2);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_48 = x_36;
} else {
 lean_dec_ref(x_36);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_33);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_3(x_2, x_5, x_6, x_8);
return x_9;
}
case 6:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_4(x_3, x_10, x_11, x_12, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_apply_1(x_4, x_1);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_2, x_14, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_4, x_18, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_2(x_12, x_22, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_2(x_5, x_26, x_28);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_box_uint64(x_32);
x_34 = lean_apply_3(x_11, x_30, x_31, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_38 = lean_box_uint64(x_37);
x_39 = lean_apply_3(x_13, x_35, x_36, x_38);
return x_39;
}
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_44 = lean_box_uint64(x_43);
x_45 = lean_apply_4(x_6, x_40, x_41, x_42, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box_uint64(x_49);
x_51 = lean_apply_4(x_9, x_46, x_47, x_48, x_50);
return x_51;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 3);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_5(x_7, x_52, x_53, x_54, x_55, x_57);
return x_58;
}
case 9:
{
lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_61 = lean_box_uint64(x_60);
x_62 = lean_apply_2(x_3, x_59, x_61);
return x_62;
}
case 10:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_66 = lean_box_uint64(x_65);
x_67 = lean_apply_3(x_10, x_63, x_64, x_66);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_72 = lean_box_uint64(x_71);
x_73 = lean_apply_4(x_8, x_68, x_69, x_70, x_72);
return x_73;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_match__3___rarg), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_getExprMVarAssignment_x3f(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_1 = x_17;
x_6 = x_16;
goto _start;
}
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(x_19, x_2, x_3, x_4, x_5, x_6);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Expr_getAppFn(x_21);
lean_dec(x_21);
switch (lean_obj_tag(x_22)) {
case 4:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(x_23, x_2, x_3, x_4, x_5, x_6);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
case 7:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_1 = x_29;
goto _start;
}
case 8:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
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
case 11:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_16, 2);
lean_dec(x_21);
x_22 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
lean_ctor_set(x_16, 2, x_22);
x_23 = lean_st_ref_set(x_1, x_15, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_11);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 3);
x_31 = lean_ctor_get(x_16, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_32 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_15, 1, x_33);
x_34 = lean_st_ref_set(x_1, x_15, x_17);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 2);
x_40 = lean_ctor_get(x_15, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_16, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 4);
lean_inc(x_44);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_45 = x_16;
} else {
 lean_dec_ref(x_16);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 5, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_44);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_39);
lean_ctor_set(x_48, 3, x_40);
x_49 = lean_st_ref_set(x_1, x_48, x_17);
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
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_11);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_saveAndResetSynthInstanceCache(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 2);
lean_dec(x_16);
lean_ctor_set(x_11, 2, x_1);
x_17 = lean_st_ref_set(x_3, x_10, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_10, 1, x_28);
x_29 = lean_st_ref_set(x_3, x_10, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 2);
x_36 = lean_ctor_get(x_10, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_41 = x_11;
} else {
 lean_dec_ref(x_11);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_1);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_36);
x_44 = lean_st_ref_set(x_3, x_43, x_12);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
lean_object* l_Lean_Meta_restoreSynthInstanceCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_restoreSynthInstanceCache(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_restoreSynthInstanceCache(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_restoreSynthInstanceCache(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_restoreSynthInstanceCache(x_9, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_Meta_restoreSynthInstanceCache(x_9, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCache___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1), 7, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_getFVarLocalDecl(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_binderInfo(x_10);
lean_dec(x_10);
x_13 = lean_box(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_15 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = lean_apply_5(x_3, x_23, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_restoreSynthInstanceCache(x_16, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l_Lean_Meta_restoreSynthInstanceCache(x_16, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___rarg___lambda__1), 9, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isForall(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_apply_7(x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_4, x_5, x_1, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(x_5, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_18 = lean_array_get_size(x_5);
x_19 = lean_expr_instantiate_rev_range(x_7, x_6, x_18, x_5);
lean_dec(x_18);
lean_dec(x_7);
lean_inc(x_5);
x_20 = lean_apply_2(x_3, x_5, x_19);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_8, 1);
lean_dec(x_22);
lean_ctor_set(x_8, 1, x_4);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_20, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_25);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_20, x_26, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_7);
x_28 = lean_array_get_size(x_5);
x_29 = lean_expr_instantiate_rev_range(x_14, x_6, x_28, x_5);
lean_dec(x_28);
lean_dec(x_14);
x_30 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = (uint8_t)((x_16 << 24) >> 61);
lean_inc(x_31);
x_34 = lean_local_ctx_mk_local_decl(x_4, x_31, x_13, x_29, x_33);
x_35 = l_Lean_mkFVar(x_31);
x_36 = lean_array_push(x_5, x_35);
x_4 = x_34;
x_5 = x_36;
x_7 = x_15;
x_12 = x_32;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_array_get_size(x_5);
x_39 = lean_expr_instantiate_rev_range(x_7, x_6, x_38, x_5);
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
lean_dec(x_2);
lean_inc(x_5);
x_40 = lean_apply_2(x_3, x_5, x_39);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_8, 1);
lean_dec(x_42);
lean_ctor_set(x_8, 1, x_4);
x_43 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_40, x_8, x_9, x_10, x_11, x_12);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_45);
x_47 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_40, x_46, x_9, x_10, x_11, x_12);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(x_5, x_2);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_38);
lean_dec(x_2);
lean_inc(x_5);
x_49 = lean_apply_2(x_3, x_5, x_39);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_8, 1);
lean_dec(x_51);
lean_ctor_set(x_8, 1, x_4);
x_52 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_49, x_8, x_9, x_10, x_11, x_12);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_4);
lean_ctor_set(x_55, 2, x_54);
x_56 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_49, x_55, x_9, x_10, x_11, x_12);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc(x_39);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 6, 1);
lean_closure_set(x_57, 0, x_39);
x_58 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_5);
x_59 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_59, 0, x_3);
lean_closure_set(x_59, 1, x_5);
lean_closure_set(x_59, 2, x_39);
lean_closure_set(x_59, 3, x_58);
lean_closure_set(x_59, 4, x_2);
lean_closure_set(x_59, 5, x_4);
lean_closure_set(x_59, 6, x_38);
x_60 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_60, 0, x_57);
lean_closure_set(x_60, 1, x_59);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_8, 1);
lean_dec(x_62);
lean_ctor_set(x_8, 1, x_4);
x_63 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_60, x_8, x_9, x_10, x_11, x_12);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_8, 0);
x_65 = lean_ctor_get(x_8, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_4);
lean_ctor_set(x_66, 2, x_65);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_60, x_66, x_9, x_10, x_11, x_12);
return x_67;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_13 = l_Lean_Meta_getFVarLocalDecl(x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(x_16, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
x_8 = x_19;
goto _start;
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg), 8, 3);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_3);
x_28 = l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(x_24, x_12, x_27, x_4, x_5, x_6, x_7, x_23);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(x_16, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
lean_dec(x_2);
x_2 = x_34;
x_8 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
lean_dec(x_2);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg), 8, 3);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_3);
x_41 = l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(x_37, x_12, x_40, x_4, x_5, x_6, x_7, x_36);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_3);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
lean_inc(x_13);
x_16 = lean_is_class(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_free_object(x_9);
x_17 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_getAppFn(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_is_class(x_13, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Lean_Expr_getAppFn(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_is_class(x_13, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_9, 0, x_37);
return x_9;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_getAppFn(x_3);
if (lean_obj_tag(x_41) == 4)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_42);
lean_inc(x_40);
x_43 = lean_is_class(x_40, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
x_44 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
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
x_48 = l_Lean_Expr_getAppFn(x_45);
lean_dec(x_45);
if (lean_obj_tag(x_48) == 4)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_49);
x_50 = lean_is_class(x_40, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_48);
lean_dec(x_40);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_1);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_42);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_39);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_39);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 2;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_7, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get_uint8(x_9, 0);
x_23 = lean_ctor_get_uint8(x_9, 1);
x_24 = lean_ctor_get_uint8(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, 4);
x_27 = lean_ctor_get_uint8(x_9, 6);
x_28 = lean_ctor_get_uint8(x_9, 7);
x_29 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_30 = 2;
x_31 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_31, 0, x_22);
lean_ctor_set_uint8(x_31, 1, x_23);
lean_ctor_set_uint8(x_31, 2, x_24);
lean_ctor_set_uint8(x_31, 3, x_25);
lean_ctor_set_uint8(x_31, 4, x_26);
lean_ctor_set_uint8(x_31, 5, x_30);
lean_ctor_set_uint8(x_31, 6, x_27);
lean_ctor_set_uint8(x_31, 7, x_28);
lean_ctor_set_uint8(x_31, 8, x_29);
lean_ctor_set(x_2, 0, x_31);
x_32 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
x_33 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_7, x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
x_45 = lean_ctor_get_uint8(x_42, 0);
x_46 = lean_ctor_get_uint8(x_42, 1);
x_47 = lean_ctor_get_uint8(x_42, 2);
x_48 = lean_ctor_get_uint8(x_42, 3);
x_49 = lean_ctor_get_uint8(x_42, 4);
x_50 = lean_ctor_get_uint8(x_42, 6);
x_51 = lean_ctor_get_uint8(x_42, 7);
x_52 = lean_ctor_get_uint8(x_42, 8);
if (lean_is_exclusive(x_42)) {
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
x_54 = 2;
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 0, 9);
} else {
 x_55 = x_53;
}
lean_ctor_set_uint8(x_55, 0, x_45);
lean_ctor_set_uint8(x_55, 1, x_46);
lean_ctor_set_uint8(x_55, 2, x_47);
lean_ctor_set_uint8(x_55, 3, x_48);
lean_ctor_set_uint8(x_55, 4, x_49);
lean_ctor_set_uint8(x_55, 5, x_54);
lean_ctor_set_uint8(x_55, 6, x_50);
lean_ctor_set_uint8(x_55, 7, x_51);
lean_ctor_set_uint8(x_55, 8, x_52);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
x_57 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
x_58 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_7, x_57, x_56, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_isForall(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = lean_apply_7(x_3, x_13, x_1, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = 1;
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_15, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Meta_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_isForall(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_2);
x_28 = l_Array_empty___closed__1;
x_29 = lean_apply_7(x_3, x_28, x_1, x_4, x_5, x_6, x_7, x_26);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = 1;
x_31 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_30, x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = l_Array_empty___closed__1;
x_37 = lean_apply_7(x_3, x_36, x_1, x_4, x_5, x_6, x_7, x_8);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l_Array_empty___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_1, x_2, x_4, x_10, x_11, x_12, x_3, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(x_1, x_2, x_3, x_4, x_5, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_isClass_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg___lambda__1), 9, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___rarg___lambda__1), 9, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_9, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_box(0);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_11, x_10, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1), 9, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_13 = lean_box(x_1);
x_14 = lean_box_uint64(x_12);
x_15 = lean_apply_8(x_6, x_13, x_2, x_3, x_4, x_9, x_10, x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = lean_box(x_1);
x_17 = lean_apply_5(x_8, x_16, x_2, x_3, x_4, x_5);
return x_17;
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 6:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_22 = lean_box(x_1);
x_23 = lean_box_uint64(x_21);
x_24 = lean_apply_8(x_6, x_22, x_2, x_3, x_4, x_18, x_19, x_20, x_23);
return x_24;
}
case 8:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_6);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_dec(x_5);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_8(x_7, x_2, x_3, x_4, x_25, x_26, x_27, x_28, x_30);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_box(x_1);
x_33 = lean_apply_5(x_8, x_32, x_2, x_3, x_4, x_5);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux_match__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_2 == 0)
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_16 = lean_array_get_size(x_4);
x_17 = lean_expr_instantiate_rev_range(x_13, x_5, x_16, x_4);
lean_dec(x_16);
lean_dec(x_13);
x_18 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = (uint8_t)((x_15 << 24) >> 61);
lean_inc(x_19);
x_22 = lean_local_ctx_mk_local_decl(x_3, x_19, x_12, x_17, x_21);
x_23 = l_Lean_mkFVar(x_19);
x_24 = lean_array_push(x_4, x_23);
x_3 = x_22;
x_4 = x_24;
x_6 = x_14;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_array_get_size(x_4);
x_27 = lean_expr_instantiate_rev_range(x_6, x_5, x_26, x_4);
lean_dec(x_26);
lean_dec(x_6);
lean_inc(x_4);
x_28 = lean_apply_2(x_1, x_4, x_27);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_7, 1);
lean_dec(x_30);
lean_ctor_set(x_7, 1, x_3);
x_31 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_28, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_33);
x_35 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_28, x_34, x_8, x_9, x_10, x_11);
return x_35;
}
}
}
else
{
switch (lean_obj_tag(x_6)) {
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_40 = lean_array_get_size(x_4);
x_41 = lean_expr_instantiate_rev_range(x_37, x_5, x_40, x_4);
lean_dec(x_40);
lean_dec(x_37);
x_42 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = (uint8_t)((x_39 << 24) >> 61);
lean_inc(x_43);
x_46 = lean_local_ctx_mk_local_decl(x_3, x_43, x_36, x_41, x_45);
x_47 = l_Lean_mkFVar(x_43);
x_48 = lean_array_push(x_4, x_47);
x_3 = x_46;
x_4 = x_48;
x_6 = x_38;
x_11 = x_44;
goto _start;
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_50 = lean_ctor_get(x_6, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_6, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 3);
lean_inc(x_53);
lean_dec(x_6);
x_54 = lean_array_get_size(x_4);
x_55 = lean_expr_instantiate_rev_range(x_51, x_5, x_54, x_4);
lean_dec(x_51);
x_56 = lean_expr_instantiate_rev_range(x_52, x_5, x_54, x_4);
lean_dec(x_54);
lean_dec(x_52);
x_57 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = 0;
lean_inc(x_58);
x_61 = lean_local_ctx_mk_let_decl(x_3, x_58, x_50, x_55, x_56, x_60);
x_62 = l_Lean_mkFVar(x_58);
x_63 = lean_array_push(x_4, x_62);
x_64 = 1;
x_2 = x_64;
x_3 = x_61;
x_4 = x_63;
x_6 = x_53;
x_11 = x_59;
goto _start;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_array_get_size(x_4);
x_67 = lean_expr_instantiate_rev_range(x_6, x_5, x_66, x_4);
lean_dec(x_66);
lean_dec(x_6);
lean_inc(x_4);
x_68 = lean_apply_2(x_1, x_4, x_67);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_7, 1);
lean_dec(x_70);
lean_ctor_set(x_7, 1, x_3);
x_71 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_68, x_7, x_8, x_9, x_10, x_11);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_ctor_get(x_7, 2);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_7);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_3);
lean_ctor_set(x_74, 2, x_73);
x_75 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_68, x_74, x_8, x_9, x_10, x_11);
return x_75;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeAux___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_10 = lean_box(x_1);
x_11 = lean_box_uint64(x_9);
x_12 = lean_apply_5(x_3, x_10, x_6, x_7, x_8, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_box(x_1);
x_14 = lean_apply_2(x_5, x_13, x_2);
return x_14;
}
}
else
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_19 = lean_box(x_1);
x_20 = lean_box_uint64(x_18);
x_21 = lean_apply_5(x_3, x_19, x_15, x_16, x_17, x_20);
return x_21;
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_3);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_dec(x_2);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_5(x_4, x_22, x_23, x_24, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_box(x_1);
x_30 = lean_apply_2(x_5, x_29, x_2);
return x_30;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_2 == 0)
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_16 = lean_array_get_size(x_4);
x_17 = lean_expr_instantiate_rev_range(x_13, x_5, x_16, x_4);
lean_dec(x_16);
lean_dec(x_13);
x_18 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = (uint8_t)((x_15 << 24) >> 61);
lean_inc(x_19);
x_22 = lean_local_ctx_mk_local_decl(x_3, x_19, x_12, x_17, x_21);
x_23 = l_Lean_mkFVar(x_19);
x_24 = lean_array_push(x_4, x_23);
x_3 = x_22;
x_4 = x_24;
x_6 = x_14;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_array_get_size(x_4);
x_27 = lean_expr_instantiate_rev_range(x_6, x_5, x_26, x_4);
lean_dec(x_26);
lean_dec(x_6);
lean_inc(x_4);
x_28 = lean_apply_2(x_1, x_4, x_27);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_7, 1);
lean_dec(x_30);
lean_ctor_set(x_7, 1, x_3);
x_31 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_28, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_33);
x_35 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_28, x_34, x_8, x_9, x_10, x_11);
return x_35;
}
}
}
else
{
switch (lean_obj_tag(x_6)) {
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_40 = lean_array_get_size(x_4);
x_41 = lean_expr_instantiate_rev_range(x_37, x_5, x_40, x_4);
lean_dec(x_40);
lean_dec(x_37);
x_42 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = (uint8_t)((x_39 << 24) >> 61);
lean_inc(x_43);
x_46 = lean_local_ctx_mk_local_decl(x_3, x_43, x_36, x_41, x_45);
x_47 = l_Lean_mkFVar(x_43);
x_48 = lean_array_push(x_4, x_47);
x_3 = x_46;
x_4 = x_48;
x_6 = x_38;
x_11 = x_44;
goto _start;
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_50 = lean_ctor_get(x_6, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_6, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 3);
lean_inc(x_53);
lean_dec(x_6);
x_54 = lean_array_get_size(x_4);
x_55 = lean_expr_instantiate_rev_range(x_51, x_5, x_54, x_4);
lean_dec(x_51);
x_56 = lean_expr_instantiate_rev_range(x_52, x_5, x_54, x_4);
lean_dec(x_54);
lean_dec(x_52);
x_57 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = 0;
lean_inc(x_58);
x_61 = lean_local_ctx_mk_let_decl(x_3, x_58, x_50, x_55, x_56, x_60);
x_62 = l_Lean_mkFVar(x_58);
x_63 = lean_array_push(x_4, x_62);
x_64 = 1;
x_2 = x_64;
x_3 = x_61;
x_4 = x_63;
x_6 = x_53;
x_11 = x_59;
goto _start;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_array_get_size(x_4);
x_67 = lean_expr_instantiate_rev_range(x_6, x_5, x_66, x_4);
lean_dec(x_66);
lean_dec(x_6);
lean_inc(x_4);
x_68 = lean_apply_2(x_1, x_4, x_67);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_7, 1);
lean_dec(x_70);
lean_ctor_set(x_7, 1, x_3);
x_71 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_68, x_7, x_8, x_9, x_10, x_11);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_ctor_get(x_7, 2);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_7);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_3);
lean_ctor_set(x_74, 2, x_73);
x_75 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_68, x_74, x_8, x_9, x_10, x_11);
return x_75;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l_Array_empty___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(x_3, x_2, x_9, x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = 1;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_2, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_2, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_lambdaTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_14 = l_Lean_mkConst(x_1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_KernelException_toMessageData___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_box(0);
x_27 = l_Lean_mkConst(x_1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_KernelException_toMessageData___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2(x_32, x_2, x_3, x_4, x_5, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_4);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = 1;
x_22 = x_2 + x_21;
x_23 = x_20;
x_24 = lean_array_uset(x_14, x_2, x_23);
x_2 = x_22;
x_3 = x_24;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getParamNames___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getParamNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = x_1;
x_11 = lean_box_usize(x_9);
x_12 = l_Lean_Meta_getParamNames___lambda__1___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = x_13;
x_15 = lean_apply_5(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_getParamNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_getParamNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_11 = l_Lean_Meta_getParamNames___closed__1;
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_getParamNames___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__3(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getParamNames___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_17 = lean_array_get_size(x_4);
x_18 = lean_expr_instantiate_rev_range(x_14, x_6, x_17, x_4);
lean_dec(x_17);
lean_dec(x_14);
x_19 = (uint8_t)((x_16 << 24) >> 61);
x_20 = l_Lean_BinderInfo_isInstImplicit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_8);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_push(x_4, x_23);
x_26 = lean_box(x_19);
x_27 = lean_array_push(x_5, x_26);
x_4 = x_25;
x_5 = x_27;
x_7 = x_15;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = 1;
lean_inc(x_8);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_29, x_13, x_8, x_9, x_10, x_11, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_4, x_31);
x_34 = lean_box(x_19);
x_35 = lean_array_push(x_5, x_34);
x_4 = x_33;
x_5 = x_35;
x_7 = x_15;
x_12 = x_32;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 2);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_array_get_size(x_4);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_expr_instantiate_rev_range(x_7, x_6, x_42, x_4);
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_7);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_12);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_7);
x_48 = lean_expr_instantiate_rev_range(x_38, x_6, x_42, x_4);
lean_dec(x_42);
lean_dec(x_38);
x_49 = (uint8_t)((x_40 << 24) >> 61);
x_50 = l_Lean_BinderInfo_isInstImplicit(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_48);
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_8);
x_52 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_51, x_3, x_37, x_8, x_9, x_10, x_11, x_12);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_array_push(x_4, x_53);
x_56 = lean_box(x_49);
x_57 = lean_array_push(x_5, x_56);
x_4 = x_55;
x_5 = x_57;
x_7 = x_39;
x_12 = x_54;
goto _start;
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = 1;
lean_inc(x_8);
x_60 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_51, x_59, x_37, x_8, x_9, x_10, x_11, x_12);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_push(x_4, x_61);
x_64 = lean_box(x_49);
x_65 = lean_array_push(x_5, x_64);
x_4 = x_63;
x_5 = x_65;
x_7 = x_39;
x_12 = x_62;
goto _start;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_get_size(x_4);
x_68 = lean_expr_instantiate_rev_range(x_7, x_6, x_67, x_4);
lean_dec(x_6);
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_12);
return x_71;
}
else
{
lean_object* x_72; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_68);
x_72 = l_Lean_Meta_whnf(x_68, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
x_76 = l_Lean_Expr_isForall(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_68);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_4);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_72, 0, x_78);
return x_72;
}
else
{
lean_free_object(x_72);
lean_dec(x_68);
x_6 = x_67;
x_7 = x_74;
x_12 = x_75;
goto _start;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_72, 0);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_72);
x_82 = l_Lean_Expr_isForall(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_5);
lean_ctor_set(x_83, 1, x_68);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_dec(x_68);
x_6 = x_67;
x_7 = x_80;
x_12 = x_81;
goto _start;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(x_13, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_empty___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(x_2, x_3, x_4, x_10, x_10, x_11, x_1, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_10, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_9, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_forallMetaTelescope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_forallMetaTelescope(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaMetaTelescope_process_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaMetaTelescope_process_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_14 = lean_array_get_size(x_2);
x_15 = lean_expr_instantiate_rev_range(x_11, x_4, x_14, x_2);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_6);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_push(x_2, x_20);
x_23 = (uint8_t)((x_13 << 24) >> 61);
x_24 = lean_box(x_23);
x_25 = lean_array_push(x_3, x_24);
x_2 = x_22;
x_3 = x_25;
x_5 = x_12;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_27 = lean_array_get_size(x_2);
x_28 = lean_expr_instantiate_rev_range(x_5, x_4, x_27, x_2);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_array_get_size(x_2);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
x_35 = lean_expr_instantiate_rev_range(x_5, x_4, x_33, x_2);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
else
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_5, 2);
x_41 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_42 = lean_expr_instantiate_rev_range(x_39, x_4, x_33, x_2);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = 0;
x_45 = lean_box(0);
lean_inc(x_6);
x_46 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_43, x_44, x_45, x_6, x_7, x_8, x_9, x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_push(x_2, x_47);
x_50 = (uint8_t)((x_41 << 24) >> 61);
x_51 = lean_box(x_50);
x_52 = lean_array_push(x_3, x_51);
x_2 = x_49;
x_3 = x_52;
x_5 = x_40;
x_10 = x_48;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
x_54 = lean_expr_instantiate_rev_range(x_5, x_4, x_33, x_2);
lean_dec(x_33);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
return x_57;
}
}
}
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaMetaTelescope_process(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_empty___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_lambdaMetaTelescope_process(x_2, x_8, x_8, x_9, x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_lambdaMetaTelescope(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_isClass_x3f(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_1);
x_15 = lean_apply_1(x_3, x_1);
x_16 = l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(x_14, x_1, x_15, x_4, x_5, x_6, x_7, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
lean_inc(x_11);
x_15 = lean_local_ctx_mk_local_decl(x_14, x_11, x_1, x_3, x_2);
x_16 = l_Lean_mkFVar(x_11);
lean_ctor_set(x_5, 1, x_15);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_11);
x_21 = lean_local_ctx_mk_local_decl(x_19, x_11, x_1, x_3, x_2);
x_22 = l_Lean_mkFVar(x_11);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_22, x_3, x_4, x_23, x_6, x_7, x_8, x_12);
return x_24;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_6);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_apply_2(x_11, lean_box(0), x_10);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_1(x_13, lean_box(0));
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_withLocalDecl___rarg___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_withLocalDecl___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_withLocalDecl___rarg(x_1, x_2, lean_box(0), x_4, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_withLocalDeclD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = 0;
lean_inc(x_2);
lean_inc(x_11);
x_16 = lean_local_ctx_mk_let_decl(x_14, x_11, x_1, x_2, x_3, x_15);
x_17 = l_Lean_mkFVar(x_11);
lean_ctor_set(x_5, 1, x_16);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_22 = 0;
lean_inc(x_2);
lean_inc(x_11);
x_23 = lean_local_ctx_mk_let_decl(x_20, x_11, x_1, x_2, x_3, x_22);
x_24 = l_Lean_mkFVar(x_11);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
x_26 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_24, x_2, x_4, x_25, x_6, x_7, x_8, x_12);
return x_26;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___rarg___lambda__1), 10, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_apply_2(x_10, lean_box(0), x_9);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_12, lean_box(0));
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_withLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___rarg), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_LocalContext_addDecl(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_LocalDecl_type(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_isClass_x3f(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_10;
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_LocalDecl_toExpr(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_push(x_1, x_19);
x_1 = x_20;
x_2 = x_10;
x_7 = x_16;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_array_get_size(x_11);
lean_inc(x_1);
x_13 = l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(x_10, x_1);
lean_inc(x_11);
lean_inc(x_13);
lean_inc(x_9);
lean_ctor_set(x_3, 1, x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_11, x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_eq(x_17, x_12);
lean_dec(x_12);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_4, x_5, x_6, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_apply_5(x_2, x_22, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_restoreSynthInstanceCache(x_20, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_restoreSynthInstanceCache(x_20, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
x_38 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_16);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_46 = lean_array_get_size(x_45);
lean_inc(x_1);
x_47 = l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(x_44, x_1);
lean_inc(x_45);
lean_inc(x_47);
lean_inc(x_43);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_45);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_48);
x_49 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_45, x_1, x_48, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_array_get_size(x_50);
x_53 = lean_nat_dec_eq(x_52, x_46);
lean_dec(x_46);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_4, x_5, x_6, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = lean_apply_5(x_2, x_57, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_restoreSynthInstanceCache(x_55, x_48, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = l_Lean_Meta_restoreSynthInstanceCache(x_55, x_48, x_4, x_5, x_6, x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_43);
x_71 = lean_apply_5(x_2, x_48, x_4, x_5, x_6, x_51);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_72 = lean_ctor_get(x_49, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_49, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_74 = x_49;
} else {
 lean_dec_ref(x_49);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_MetavarContext_incDepth(x_19);
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_3, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_setMCtx(x_12, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_setMCtx(x_12, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
x_40 = lean_ctor_get(x_16, 2);
x_41 = lean_ctor_get(x_16, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_42 = l_Lean_MetavarContext_incDepth(x_38);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_st_ref_set(x_3, x_43, x_17);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_setMCtx(x_12, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = l_Lean_Meta_setMCtx(x_12, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_2, lean_box(0), x_1);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_eqv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_17;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_2);
x_13 = lean_array_get_size(x_10);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
if (x_14 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_2);
x_18 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_restoreSynthInstanceCache(x_19, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_Lean_Meta_restoreSynthInstanceCache(x_19, x_4, x_5, x_6, x_7, x_30);
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
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(x_2, x_10, lean_box(0), x_2, x_10, x_36);
lean_dec(x_10);
lean_dec(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
x_56 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_11);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_4, 0);
lean_inc(x_57);
lean_dec(x_4);
lean_inc(x_2);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_2);
if (x_14 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_2);
x_59 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_58);
x_62 = lean_apply_5(x_3, x_58, x_5, x_6, x_7, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_restoreSynthInstanceCache(x_60, x_58, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = l_Lean_Meta_restoreSynthInstanceCache(x_60, x_58, x_5, x_6, x_7, x_70);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_58);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(x_2, x_10, lean_box(0), x_2, x_10, x_75);
lean_dec(x_10);
lean_dec(x_2);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_58);
x_80 = lean_apply_5(x_3, x_58, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_restoreSynthInstanceCache(x_78, x_58, x_5, x_6, x_7, x_82);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_58);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_dec(x_80);
x_89 = l_Lean_Meta_restoreSynthInstanceCache(x_78, x_58, x_5, x_6, x_7, x_88);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_58);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
 lean_ctor_set_tag(x_92, 1);
}
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; 
x_93 = lean_apply_5(x_3, x_58, x_5, x_6, x_7, x_11);
return x_93;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_withLCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___rarg___lambda__1), 9, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_setMCtx(x_1, x_3, x_4, x_5, x_6, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_setMCtx(x_13, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_Meta_setMCtx(x_13, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___rarg___lambda__1), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_withMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 0, x_10);
lean_ctor_set_uint8(x_8, 1, x_10);
lean_ctor_set_uint8(x_8, 2, x_10);
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get_uint8(x_8, 3);
x_21 = lean_ctor_get_uint8(x_8, 4);
x_22 = lean_ctor_get_uint8(x_8, 5);
x_23 = lean_ctor_get_uint8(x_8, 6);
x_24 = lean_ctor_get_uint8(x_8, 7);
x_25 = lean_ctor_get_uint8(x_8, 8);
lean_dec(x_8);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, 3, x_20);
lean_ctor_set_uint8(x_27, 4, x_21);
lean_ctor_set_uint8(x_27, 5, x_22);
lean_ctor_set_uint8(x_27, 6, x_23);
lean_ctor_set_uint8(x_27, 7, x_24);
lean_ctor_set_uint8(x_27, 8, x_25);
lean_ctor_set(x_2, 0, x_27);
x_28 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_40 = lean_ctor_get_uint8(x_37, 3);
x_41 = lean_ctor_get_uint8(x_37, 4);
x_42 = lean_ctor_get_uint8(x_37, 5);
x_43 = lean_ctor_get_uint8(x_37, 6);
x_44 = lean_ctor_get_uint8(x_37, 7);
x_45 = lean_ctor_get_uint8(x_37, 8);
if (lean_is_exclusive(x_37)) {
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
x_47 = 1;
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 0, 9);
} else {
 x_48 = x_46;
}
lean_ctor_set_uint8(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, 2, x_47);
lean_ctor_set_uint8(x_48, 3, x_40);
lean_ctor_set_uint8(x_48, 4, x_41);
lean_ctor_set_uint8(x_48, 5, x_42);
lean_ctor_set_uint8(x_48, 6, x_43);
lean_ctor_set_uint8(x_48, 7, x_44);
lean_ctor_set_uint8(x_48, 8, x_45);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_39);
x_50 = lean_apply_5(x_1, x_49, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_approxDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 0, x_11);
lean_ctor_set_uint8(x_9, 1, x_11);
lean_ctor_set_uint8(x_9, 2, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
x_26 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, 3, x_21);
lean_ctor_set_uint8(x_28, 4, x_22);
lean_ctor_set_uint8(x_28, 5, x_23);
lean_ctor_set_uint8(x_28, 6, x_24);
lean_ctor_set_uint8(x_28, 7, x_25);
lean_ctor_set_uint8(x_28, 8, x_26);
lean_ctor_set(x_3, 0, x_28);
x_29 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_41 = lean_ctor_get_uint8(x_38, 3);
x_42 = lean_ctor_get_uint8(x_38, 4);
x_43 = lean_ctor_get_uint8(x_38, 5);
x_44 = lean_ctor_get_uint8(x_38, 6);
x_45 = lean_ctor_get_uint8(x_38, 7);
x_46 = lean_ctor_get_uint8(x_38, 8);
if (lean_is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
x_48 = 1;
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 0, 9);
} else {
 x_49 = x_47;
}
lean_ctor_set_uint8(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, 2, x_48);
lean_ctor_set_uint8(x_49, 3, x_41);
lean_ctor_set_uint8(x_49, 4, x_42);
lean_ctor_set_uint8(x_49, 5, x_43);
lean_ctor_set_uint8(x_49, 6, x_44);
lean_ctor_set_uint8(x_49, 7, x_45);
lean_ctor_set_uint8(x_49, 8, x_46);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
x_51 = lean_apply_7(x_2, lean_box(0), x_1, x_50, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
lean_object* l_Lean_Meta_approxDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_approxDefEq___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_approxDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_approxDefEq___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 0, x_10);
lean_ctor_set_uint8(x_8, 1, x_10);
lean_ctor_set_uint8(x_8, 2, x_10);
lean_ctor_set_uint8(x_8, 3, x_10);
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get_uint8(x_8, 4);
x_21 = lean_ctor_get_uint8(x_8, 5);
x_22 = lean_ctor_get_uint8(x_8, 6);
x_23 = lean_ctor_get_uint8(x_8, 7);
x_24 = lean_ctor_get_uint8(x_8, 8);
lean_dec(x_8);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, 2, x_25);
lean_ctor_set_uint8(x_26, 3, x_25);
lean_ctor_set_uint8(x_26, 4, x_20);
lean_ctor_set_uint8(x_26, 5, x_21);
lean_ctor_set_uint8(x_26, 6, x_22);
lean_ctor_set_uint8(x_26, 7, x_23);
lean_ctor_set_uint8(x_26, 8, x_24);
lean_ctor_set(x_2, 0, x_26);
x_27 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_39 = lean_ctor_get_uint8(x_36, 4);
x_40 = lean_ctor_get_uint8(x_36, 5);
x_41 = lean_ctor_get_uint8(x_36, 6);
x_42 = lean_ctor_get_uint8(x_36, 7);
x_43 = lean_ctor_get_uint8(x_36, 8);
if (lean_is_exclusive(x_36)) {
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
x_45 = 1;
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 0, 9);
} else {
 x_46 = x_44;
}
lean_ctor_set_uint8(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, 2, x_45);
lean_ctor_set_uint8(x_46, 3, x_45);
lean_ctor_set_uint8(x_46, 4, x_39);
lean_ctor_set_uint8(x_46, 5, x_40);
lean_ctor_set_uint8(x_46, 6, x_41);
lean_ctor_set_uint8(x_46, 7, x_42);
lean_ctor_set_uint8(x_46, 8, x_43);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_38);
x_48 = lean_apply_5(x_1, x_47, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_fullApproxDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 0, x_11);
lean_ctor_set_uint8(x_9, 1, x_11);
lean_ctor_set_uint8(x_9, 2, x_11);
lean_ctor_set_uint8(x_9, 3, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get_uint8(x_9, 4);
x_22 = lean_ctor_get_uint8(x_9, 5);
x_23 = lean_ctor_get_uint8(x_9, 6);
x_24 = lean_ctor_get_uint8(x_9, 7);
x_25 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, 3, x_26);
lean_ctor_set_uint8(x_27, 4, x_21);
lean_ctor_set_uint8(x_27, 5, x_22);
lean_ctor_set_uint8(x_27, 6, x_23);
lean_ctor_set_uint8(x_27, 7, x_24);
lean_ctor_set_uint8(x_27, 8, x_25);
lean_ctor_set(x_3, 0, x_27);
x_28 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_40 = lean_ctor_get_uint8(x_37, 4);
x_41 = lean_ctor_get_uint8(x_37, 5);
x_42 = lean_ctor_get_uint8(x_37, 6);
x_43 = lean_ctor_get_uint8(x_37, 7);
x_44 = lean_ctor_get_uint8(x_37, 8);
if (lean_is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 9);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, 2, x_46);
lean_ctor_set_uint8(x_47, 3, x_46);
lean_ctor_set_uint8(x_47, 4, x_40);
lean_ctor_set_uint8(x_47, 5, x_41);
lean_ctor_set_uint8(x_47, 6, x_42);
lean_ctor_set_uint8(x_47, 7, x_43);
lean_ctor_set_uint8(x_47, 8, x_44);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_39);
x_49 = lean_apply_7(x_2, lean_box(0), x_1, x_48, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
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
}
lean_object* l_Lean_Meta_fullApproxDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_fullApproxDefEq___rarg___lambda__1), 7, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_fullApproxDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_fullApproxDefEq___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_normalizeLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1;
x_8 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2;
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3;
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4;
x_11 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5;
x_12 = l_Lean_MetavarContext_instantiateLevelMVars_match__2___rarg(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_apply_5(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Level_normalize(x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_Level_normalize(x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_assignLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Lean_MetavarContext_assignLevel(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_27 = l_Lean_MetavarContext_assignLevel(x_23, x_1, x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_assignLevelMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 2;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
lean_dec(x_8);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_29, 0, x_20);
lean_ctor_set_uint8(x_29, 1, x_21);
lean_ctor_set_uint8(x_29, 2, x_22);
lean_ctor_set_uint8(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, 4, x_24);
lean_ctor_set_uint8(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, 6, x_25);
lean_ctor_set_uint8(x_29, 7, x_26);
lean_ctor_set_uint8(x_29, 8, x_27);
lean_ctor_set(x_2, 0, x_29);
x_30 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_42 = lean_ctor_get_uint8(x_39, 0);
x_43 = lean_ctor_get_uint8(x_39, 1);
x_44 = lean_ctor_get_uint8(x_39, 2);
x_45 = lean_ctor_get_uint8(x_39, 3);
x_46 = lean_ctor_get_uint8(x_39, 4);
x_47 = lean_ctor_get_uint8(x_39, 6);
x_48 = lean_ctor_get_uint8(x_39, 7);
x_49 = lean_ctor_get_uint8(x_39, 8);
if (lean_is_exclusive(x_39)) {
 x_50 = x_39;
} else {
 lean_dec_ref(x_39);
 x_50 = lean_box(0);
}
x_51 = 2;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 0, 9);
} else {
 x_52 = x_50;
}
lean_ctor_set_uint8(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, 1, x_43);
lean_ctor_set_uint8(x_52, 2, x_44);
lean_ctor_set_uint8(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, 4, x_46);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_47);
lean_ctor_set_uint8(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, 8, x_49);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_53, 2, x_41);
x_54 = l_Lean_Meta_whnf(x_1, x_53, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l_Lean_Meta_whnfD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
lean_dec(x_8);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_29, 0, x_20);
lean_ctor_set_uint8(x_29, 1, x_21);
lean_ctor_set_uint8(x_29, 2, x_22);
lean_ctor_set_uint8(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, 4, x_24);
lean_ctor_set_uint8(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, 6, x_25);
lean_ctor_set_uint8(x_29, 7, x_26);
lean_ctor_set_uint8(x_29, 8, x_27);
lean_ctor_set(x_2, 0, x_29);
x_30 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_42 = lean_ctor_get_uint8(x_39, 0);
x_43 = lean_ctor_get_uint8(x_39, 1);
x_44 = lean_ctor_get_uint8(x_39, 2);
x_45 = lean_ctor_get_uint8(x_39, 3);
x_46 = lean_ctor_get_uint8(x_39, 4);
x_47 = lean_ctor_get_uint8(x_39, 6);
x_48 = lean_ctor_get_uint8(x_39, 7);
x_49 = lean_ctor_get_uint8(x_39, 8);
if (lean_is_exclusive(x_39)) {
 x_50 = x_39;
} else {
 lean_dec_ref(x_39);
 x_50 = lean_box(0);
}
x_51 = 1;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 0, 9);
} else {
 x_52 = x_50;
}
lean_ctor_set_uint8(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, 1, x_43);
lean_ctor_set_uint8(x_52, 2, x_44);
lean_ctor_set_uint8(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, 4, x_46);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_47);
lean_ctor_set_uint8(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, 8, x_49);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_53, 2, x_41);
x_54 = l_Lean_Meta_whnf(x_1, x_53, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l_Lean_Meta_whnfI(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 3;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
lean_dec(x_8);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_29, 0, x_20);
lean_ctor_set_uint8(x_29, 1, x_21);
lean_ctor_set_uint8(x_29, 2, x_22);
lean_ctor_set_uint8(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, 4, x_24);
lean_ctor_set_uint8(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, 6, x_25);
lean_ctor_set_uint8(x_29, 7, x_26);
lean_ctor_set_uint8(x_29, 8, x_27);
lean_ctor_set(x_2, 0, x_29);
x_30 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_42 = lean_ctor_get_uint8(x_39, 0);
x_43 = lean_ctor_get_uint8(x_39, 1);
x_44 = lean_ctor_get_uint8(x_39, 2);
x_45 = lean_ctor_get_uint8(x_39, 3);
x_46 = lean_ctor_get_uint8(x_39, 4);
x_47 = lean_ctor_get_uint8(x_39, 6);
x_48 = lean_ctor_get_uint8(x_39, 7);
x_49 = lean_ctor_get_uint8(x_39, 8);
if (lean_is_exclusive(x_39)) {
 x_50 = x_39;
} else {
 lean_dec_ref(x_39);
 x_50 = lean_box(0);
}
x_51 = 3;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 0, 9);
} else {
 x_52 = x_50;
}
lean_ctor_set_uint8(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, 1, x_43);
lean_ctor_set_uint8(x_52, 2, x_44);
lean_ctor_set_uint8(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, 4, x_46);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_47);
lean_ctor_set_uint8(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, 8, x_49);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_53, 2, x_41);
x_54 = l_Lean_Meta_whnf(x_1, x_53, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l_Lean_Meta_setInlineAttribute_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_setInlineAttribute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_setInlineAttribute_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_5, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_st_ref_set(x_5, x_22, x_9);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
lean_object* l_Lean_Meta_setInlineAttribute(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_inlineAttrs;
x_13 = lean_box(x_2);
x_14 = l_Lean_EnumAttributes_setValue___rarg(x_12, x_11, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_17, x_3, x_4, x_5, x_6, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_19, x_3, x_4, x_5, x_6, x_10);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_setInlineAttribute(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid instantiateForall, too many parameters");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = lean_expr_instantiate1(x_16, x_12);
lean_dec(x_12);
lean_dec(x_16);
x_2 = x_18;
x_3 = x_19;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_2);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3;
x_23 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid instantiateLambda, too many parameters");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 6)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = lean_expr_instantiate1(x_16, x_12);
lean_dec(x_12);
lean_dec(x_16);
x_2 = x_18;
x_3 = x_19;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_2);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3;
x_23 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_dependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MetavarContext_exprDependsOn(x_13, x_1, x_2);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MetavarContext_exprDependsOn(x_19, x_1, x_2);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
lean_object* l_Lean_Meta_dependsOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_dependsOn(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_5, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_st_ref_get(x_5, x_15);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_ppExpr(x_22, x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_io_error_to_string(x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_19);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_io_error_to_string(x_36);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_19);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
}
lean_object* l_Lean_Meta_ppExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_5, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_st_ref_set(x_5, x_22, x_9);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
lean_object* l_Lean_Meta_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_6, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(x_11, x_3, x_4, x_5, x_6, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Meta_setMCtx(x_17, x_3, x_4, x_5, x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
}
}
lean_object* l_Lean_Meta_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_orelse___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Meta_orelse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_instOrElseMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_orelse___rarg), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_instOrElseMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instOrElseMetaM___closed__1;
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_apply_5(x_1, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(x_13, x_5, x_6, x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_setMCtx(x_19, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_apply_5(x_2, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_apply_2(x_3, x_27, x_34);
x_37 = lean_apply_2(x_4, x_28, x_35);
lean_ctor_set(x_30, 1, x_37);
lean_ctor_set(x_30, 0, x_36);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_apply_2(x_3, x_27, x_38);
x_41 = lean_apply_2(x_4, x_28, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_46 = x_30;
} else {
 lean_dec_ref(x_30);
 x_46 = lean_box(0);
}
x_47 = lean_apply_2(x_3, x_27, x_44);
x_48 = lean_apply_2(x_4, x_28, x_45);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_29);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_29, 0);
lean_dec(x_52);
return x_29;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_30);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_25);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_25, 0);
lean_dec(x_56);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
lean_dec(x_25);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_orelseMergeErrors___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = lean_apply_7(x_5, lean_box(0), x_1, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_setEnv___at_Lean_Meta_orelse___spec__1(x_14, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_setMCtx(x_20, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_apply_7(x_5, lean_box(0), x_2, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_apply_2(x_3, x_28, x_35);
x_38 = lean_apply_2(x_4, x_29, x_36);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_37);
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_apply_2(x_3, x_28, x_39);
x_42 = lean_apply_2(x_4, x_29, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_47 = x_31;
} else {
 lean_dec_ref(x_31);
 x_47 = lean_box(0);
}
x_48 = lean_apply_2(x_3, x_28, x_45);
x_49 = lean_apply_2(x_4, x_29, x_46);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_dec(x_53);
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_26, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* l_Lean_Meta_orelseMergeErrors___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_orelseMergeErrors___rarg___lambda__1), 10, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_orelseMergeErrors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_orelseMergeErrors___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_mapErrorImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Meta_mapErrorImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mapErrorImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_apply_1(x_2, x_13);
lean_ctor_set(x_9, 1, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_apply_1(x_2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_22 = x_9;
} else {
 lean_dec_ref(x_9);
 x_22 = lean_box(0);
}
x_23 = lean_apply_1(x_2, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Meta_mapErrorImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mapErrorImp___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mapError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_mapErrorImp___rarg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_mapError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mapError___rarg___lambda__1), 8, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mapError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_mapError___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhenSome_x3f_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_StateRefT_x27_instMonadLiftStateRefT_x27___closed__1;
x_2 = l_Lean_Core_instMonadEnvCoreM;
x_3 = l_Lean_instMonadEnv___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1;
x_2 = l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2;
x_3 = l_Lean_instMonadEnv___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_33; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_5, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3;
lean_inc(x_10);
x_37 = l_Lean_setEnv___rarg(x_36, x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_apply_5(x_37, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_10);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Meta_setMCtx(x_16, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_17 = x_47;
x_18 = x_48;
goto block_32;
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_33, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_33, 0, x_53);
return x_33;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_56 = x_34;
} else {
 lean_dec_ref(x_34);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_33, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_dec(x_33);
x_17 = x_59;
x_18 = x_60;
goto block_32;
}
block_32:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3;
x_20 = l_Lean_setEnv___rarg(x_19, x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_5(x_20, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_setMCtx(x_16, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_17);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhenSome_x3f___rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_LOption(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Class(lean_object*);
lean_object* initialize_Lean_ReducibilityAttrs(lean_object*);
lean_object* initialize_Lean_Util_Trace(lean_object*);
lean_object* initialize_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Lean_Util_PPExt(lean_object*);
lean_object* initialize_Lean_Util_OccursCheck(lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(lean_object*);
lean_object* initialize_Lean_Meta_TransparencyMode(lean_object*);
lean_object* initialize_Lean_Meta_DiscrTreeTypes(lean_object*);
lean_object* initialize_Lean_Eval(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Class(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReducibilityAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_OccursCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_TransparencyMode(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTreeTypes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Eval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_isDefEqStuckExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_isDefEqStuckExceptionId);
lean_dec_ref(res);
l_Lean_Meta_Config_foApprox___default = _init_l_Lean_Meta_Config_foApprox___default();
l_Lean_Meta_Config_ctxApprox___default = _init_l_Lean_Meta_Config_ctxApprox___default();
l_Lean_Meta_Config_quasiPatternApprox___default = _init_l_Lean_Meta_Config_quasiPatternApprox___default();
l_Lean_Meta_Config_constApprox___default = _init_l_Lean_Meta_Config_constApprox___default();
l_Lean_Meta_Config_isDefEqStuckEx___default = _init_l_Lean_Meta_Config_isDefEqStuckEx___default();
l_Lean_Meta_Config_transparency___default = _init_l_Lean_Meta_Config_transparency___default();
l_Lean_Meta_Config_zetaNonDep___default = _init_l_Lean_Meta_Config_zetaNonDep___default();
l_Lean_Meta_Config_trackZeta___default = _init_l_Lean_Meta_Config_trackZeta___default();
l_Lean_Meta_Config_unificationHints___default = _init_l_Lean_Meta_Config_unificationHints___default();
l_Lean_Meta_ParamInfo_implicit___default = _init_l_Lean_Meta_ParamInfo_implicit___default();
l_Lean_Meta_ParamInfo_instImplicit___default = _init_l_Lean_Meta_ParamInfo_instImplicit___default();
l_Lean_Meta_ParamInfo_hasFwdDeps___default = _init_l_Lean_Meta_ParamInfo_hasFwdDeps___default();
l_Lean_Meta_ParamInfo_backDeps___default = _init_l_Lean_Meta_ParamInfo_backDeps___default();
lean_mark_persistent(l_Lean_Meta_ParamInfo_backDeps___default);
l_Lean_Meta_instInhabitedParamInfo___closed__1 = _init_l_Lean_Meta_instInhabitedParamInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedParamInfo___closed__1);
l_Lean_Meta_instInhabitedParamInfo = _init_l_Lean_Meta_instInhabitedParamInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedParamInfo);
l_Lean_Meta_FunInfo_paramInfo___default = _init_l_Lean_Meta_FunInfo_paramInfo___default();
lean_mark_persistent(l_Lean_Meta_FunInfo_paramInfo___default);
l_Lean_Meta_FunInfo_resultDeps___default = _init_l_Lean_Meta_FunInfo_resultDeps___default();
lean_mark_persistent(l_Lean_Meta_FunInfo_resultDeps___default);
l_Lean_Meta_instInhabitedInfoCacheKey___closed__1 = _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedInfoCacheKey___closed__1);
l_Lean_Meta_instInhabitedInfoCacheKey = _init_l_Lean_Meta_instInhabitedInfoCacheKey();
lean_mark_persistent(l_Lean_Meta_instInhabitedInfoCacheKey);
l_Lean_Meta_instBEqInfoCacheKey___closed__1 = _init_l_Lean_Meta_instBEqInfoCacheKey___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqInfoCacheKey___closed__1);
l_Lean_Meta_instBEqInfoCacheKey = _init_l_Lean_Meta_instBEqInfoCacheKey();
lean_mark_persistent(l_Lean_Meta_instBEqInfoCacheKey);
l_Lean_Meta_Cache_inferType___default___closed__1 = _init_l_Lean_Meta_Cache_inferType___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Cache_inferType___default___closed__1);
l_Lean_Meta_Cache_inferType___default = _init_l_Lean_Meta_Cache_inferType___default();
lean_mark_persistent(l_Lean_Meta_Cache_inferType___default);
l_Lean_Meta_Cache_funInfo___default___closed__1 = _init_l_Lean_Meta_Cache_funInfo___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Cache_funInfo___default___closed__1);
l_Lean_Meta_Cache_funInfo___default___closed__2 = _init_l_Lean_Meta_Cache_funInfo___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Cache_funInfo___default___closed__2);
l_Lean_Meta_Cache_funInfo___default = _init_l_Lean_Meta_Cache_funInfo___default();
lean_mark_persistent(l_Lean_Meta_Cache_funInfo___default);
l_Lean_Meta_Cache_synthInstance___default___closed__1 = _init_l_Lean_Meta_Cache_synthInstance___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Cache_synthInstance___default___closed__1);
l_Lean_Meta_Cache_synthInstance___default = _init_l_Lean_Meta_Cache_synthInstance___default();
lean_mark_persistent(l_Lean_Meta_Cache_synthInstance___default);
l_Lean_Meta_Cache_whnfDefault___default = _init_l_Lean_Meta_Cache_whnfDefault___default();
lean_mark_persistent(l_Lean_Meta_Cache_whnfDefault___default);
l_Lean_Meta_Cache_whnfAll___default = _init_l_Lean_Meta_Cache_whnfAll___default();
lean_mark_persistent(l_Lean_Meta_Cache_whnfAll___default);
l_Lean_Meta_instInhabitedCache___closed__1 = _init_l_Lean_Meta_instInhabitedCache___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCache___closed__1);
l_Lean_Meta_instInhabitedCache = _init_l_Lean_Meta_instInhabitedCache();
lean_mark_persistent(l_Lean_Meta_instInhabitedCache);
l_Lean_Meta_State_mctx___default = _init_l_Lean_Meta_State_mctx___default();
lean_mark_persistent(l_Lean_Meta_State_mctx___default);
l_Lean_Meta_State_cache___default = _init_l_Lean_Meta_State_cache___default();
lean_mark_persistent(l_Lean_Meta_State_cache___default);
l_Lean_Meta_State_zetaFVarIds___default = _init_l_Lean_Meta_State_zetaFVarIds___default();
lean_mark_persistent(l_Lean_Meta_State_zetaFVarIds___default);
l_Lean_Meta_State_postponed___default = _init_l_Lean_Meta_State_postponed___default();
lean_mark_persistent(l_Lean_Meta_State_postponed___default);
l_Lean_Meta_instInhabitedState___closed__1 = _init_l_Lean_Meta_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedState___closed__1);
l_Lean_Meta_instInhabitedState = _init_l_Lean_Meta_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_instInhabitedState);
l_Lean_Meta_Context_config___default___closed__1 = _init_l_Lean_Meta_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Context_config___default___closed__1);
l_Lean_Meta_Context_config___default = _init_l_Lean_Meta_Context_config___default();
lean_mark_persistent(l_Lean_Meta_Context_config___default);
l_Lean_Meta_Context_lctx___default = _init_l_Lean_Meta_Context_lctx___default();
lean_mark_persistent(l_Lean_Meta_Context_lctx___default);
l_Lean_Meta_Context_localInstances___default = _init_l_Lean_Meta_Context_localInstances___default();
lean_mark_persistent(l_Lean_Meta_Context_localInstances___default);
l_Lean_Meta_instMonadLCtxMetaM___closed__1 = _init_l_Lean_Meta_instMonadLCtxMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instMonadLCtxMetaM___closed__1);
l_Lean_Meta_instMonadLCtxMetaM___closed__2 = _init_l_Lean_Meta_instMonadLCtxMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instMonadLCtxMetaM___closed__2);
l_Lean_Meta_instMonadLCtxMetaM___closed__3 = _init_l_Lean_Meta_instMonadLCtxMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instMonadLCtxMetaM___closed__3);
l_Lean_Meta_instMonadLCtxMetaM = _init_l_Lean_Meta_instMonadLCtxMetaM();
lean_mark_persistent(l_Lean_Meta_instMonadLCtxMetaM);
l_Lean_Meta_instMonadMCtxMetaM___closed__1 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__1);
l_Lean_Meta_instMonadMCtxMetaM___closed__2 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__2);
l_Lean_Meta_instMonadMCtxMetaM___closed__3 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__3);
l_Lean_Meta_instMonadMCtxMetaM___closed__4 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__4();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__4);
l_Lean_Meta_instMonadMCtxMetaM___closed__5 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__5();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__5);
l_Lean_Meta_instMonadMCtxMetaM = _init_l_Lean_Meta_instMonadMCtxMetaM();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM);
l_Lean_Meta_instAddMessageContextMetaM___closed__1 = _init_l_Lean_Meta_instAddMessageContextMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instAddMessageContextMetaM___closed__1);
l_Lean_Meta_instAddMessageContextMetaM = _init_l_Lean_Meta_instAddMessageContextMetaM();
lean_mark_persistent(l_Lean_Meta_instAddMessageContextMetaM);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2);
l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1 = _init_l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949____closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_949_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_whnfRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_whnfRef);
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000____closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1000_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_inferTypeRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_inferTypeRef);
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051____closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1051_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_isExprDefEqAuxRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_isExprDefEqAuxRef);
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110____closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1110_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthPendingRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthPendingRef);
lean_dec_ref(res);
l_Lean_Meta_getMVarDecl___closed__1 = _init_l_Lean_Meta_getMVarDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___closed__1);
l_Lean_Meta_getMVarDecl___closed__2 = _init_l_Lean_Meta_getMVarDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___closed__2);
l_Lean_Meta_isReadOnlyLevelMVar___closed__1 = _init_l_Lean_Meta_isReadOnlyLevelMVar___closed__1();
lean_mark_persistent(l_Lean_Meta_isReadOnlyLevelMVar___closed__1);
l_Lean_Meta_isReadOnlyLevelMVar___closed__2 = _init_l_Lean_Meta_isReadOnlyLevelMVar___closed__2();
lean_mark_persistent(l_Lean_Meta_isReadOnlyLevelMVar___closed__2);
l_Lean_Meta_throwUnknownFVar___rarg___closed__1 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__1);
l_Lean_Meta_throwUnknownFVar___rarg___closed__2 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__2);
l_Lean_Meta_getLocalDeclFromUserName___closed__1 = _init_l_Lean_Meta_getLocalDeclFromUserName___closed__1();
lean_mark_persistent(l_Lean_Meta_getLocalDeclFromUserName___closed__1);
l_Lean_Meta_getLocalDeclFromUserName___closed__2 = _init_l_Lean_Meta_getLocalDeclFromUserName___closed__2();
lean_mark_persistent(l_Lean_Meta_getLocalDeclFromUserName___closed__2);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__1);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__2);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__3);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__4);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___closed__5);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__1);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__2);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__3);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__4);
l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5 = _init_l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5();
lean_mark_persistent(l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1);
l_Lean_Meta_liftMkBindingM___rarg___closed__1 = _init_l_Lean_Meta_liftMkBindingM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_liftMkBindingM___rarg___closed__1);
l_Lean_Meta_liftMkBindingM___rarg___closed__2 = _init_l_Lean_Meta_liftMkBindingM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_liftMkBindingM___rarg___closed__2);
l_Lean_Meta_liftMkBindingM___rarg___closed__3 = _init_l_Lean_Meta_liftMkBindingM___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_liftMkBindingM___rarg___closed__3);
l_Lean_Meta_mkArrow___closed__1 = _init_l_Lean_Meta_mkArrow___closed__1();
lean_mark_persistent(l_Lean_Meta_mkArrow___closed__1);
l_Lean_Meta_mkArrow___closed__2 = _init_l_Lean_Meta_mkArrow___closed__2();
lean_mark_persistent(l_Lean_Meta_mkArrow___closed__2);
l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__1);
l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__2);
l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___closed__3);
l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1);
l_Lean_Meta_getParamNames___lambda__1___boxed__const__1 = _init_l_Lean_Meta_getParamNames___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_getParamNames___lambda__1___boxed__const__1);
l_Lean_Meta_getParamNames___closed__1 = _init_l_Lean_Meta_getParamNames___closed__1();
lean_mark_persistent(l_Lean_Meta_getParamNames___closed__1);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__3);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__3);
l_Lean_Meta_instOrElseMetaM___closed__1 = _init_l_Lean_Meta_instOrElseMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instOrElseMetaM___closed__1);
l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1 = _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___rarg___closed__1);
l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2 = _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___rarg___closed__2);
l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3 = _init_l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
