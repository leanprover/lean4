// Lean compiler output
// Module: Lean.Meta.Basic
// Imports: Init Lean.Data.LOption Lean.Environment Lean.Class Lean.ReducibilityAttrs Lean.Util.Trace Lean.Util.RecDepth Lean.Util.Closure Lean.Compiler.InlineAttrs Lean.Meta.Exception Lean.Meta.TransparencyMode Lean.Meta.DiscrTreeTypes Lean.Eval Lean.CoreM
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
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_InfoCacheKey_Hashable(lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDecl(lean_object*);
extern lean_object* l_Std_PersistentHashMap_empty___rarg___closed__2;
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addTraceContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4(lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkSynthPendingRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_setInlineAttribute___rarg___closed__2;
lean_object* l_Lean_Meta_Lean_MonadError;
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_10__resettingSynthInstanceCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses(lean_object*);
uint8_t l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapMetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_Inhabited;
lean_object* l_Lean_Meta_mkForallUsedOnly___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_InternalExceptionId_toString___closed__1;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Basic_29__withMCtxImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___boxed(lean_object**);
extern lean_object* l_Lean_Core_Lean_MonadNameGenerator;
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_29__withMCtxImpl(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_savingCache(lean_object*);
lean_object* l_Lean_Meta_hasEval___rarg___closed__1;
lean_object* l_Lean_Meta_getParamNamesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_17__forallTelescopeImpl(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl(lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasEval___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_metavar_ctx_is_delayed_assigned(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_MonadIO(lean_object*);
lean_object* l_Lean_MetavarContext_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope(lean_object*);
lean_object* l_Lean_Meta_elimMVarDeps(lean_object*);
lean_object* l_Lean_MetavarContext_setMVarKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getTransparency___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2;
lean_object* l___private_Lean_Meta_Basic_26__withNewMCtxDepthImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_24__withLetDeclImpl(lean_object*);
lean_object* l_Lean_Meta_forallTelescope(lean_object*);
lean_object* l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Meta_mkFreshTypeMVar___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_31__fullApproxDefEqImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_fullApproxDefEq(lean_object*);
lean_object* l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_28__withMVarContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_delayed_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3(lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__3;
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*);
lean_object* l_Lean_Meta_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_mkWHNFRef___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducible___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6;
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_fullApproxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_renameMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___closed__1;
lean_object* l_Lean_Meta_whnfD___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1;
lean_object* l_Lean_MetavarContext_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isReducible(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3(lean_object*);
extern lean_object* l_Lean_Core_Lean_MonadError;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Meta_InfoCacheKey_Hashable___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_withMVarContext(lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___rarg(lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapMetaM(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3;
lean_object* l_Lean_Meta_withTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_22__withNewFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx(lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5;
lean_object* l_Lean_Meta_setMVarKind___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1(lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Meta_normalizeLevel(lean_object*);
lean_object* l_Lean_Meta_shouldReduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel___rarg___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM(lean_object*);
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimMVarDeps___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_inlineAttrs;
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3;
lean_object* l_Lean_Meta_getConfig___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_Inhabited___closed__1;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_map2MetaM(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkSynthPendingRef(lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1(lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Exception_inhabited___closed__1;
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1___closed__1;
lean_object* l_Lean_Meta_MetaM_toIO(lean_object*);
lean_object* l___private_Lean_Meta_Basic_7__savingCacheImpl(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_inhabited;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6;
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1;
uint8_t l_Lean_Meta_InfoCacheKey_HasBeq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownConstant___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1___closed__2;
lean_object* l_Lean_Meta_getMVarDecl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2;
lean_object* l_Lean_Meta_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___closed__1;
lean_object* l_Lean_Meta_inferType___rarg(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___closed__3;
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MonadIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3;
lean_object* l_Lean_Meta_MetaM_run_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl(lean_object*);
lean_object* l_StateRefT_x27_MonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency(lean_object*);
lean_object* l_Lean_Meta_renameMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1;
lean_object* l_Lean_Meta_mapMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSynthPendingRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
lean_object* l_Lean_Meta_mkForallUsedOnly(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_30__approxDefEqImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstanceImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___closed__4;
lean_object* l_Lean_Meta_ParamInfo_inhabited___closed__1;
lean_object* l___private_Lean_Meta_Basic_31__fullApproxDefEqImpl(lean_object*);
lean_object* l_Lean_Meta_liftMetaM___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map2MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_10__resettingSynthInstanceCacheImpl(lean_object*);
lean_object* l_Lean_Meta_renameMVar(lean_object*);
lean_object* l_Lean_Meta_getParamNamesImpl___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__1;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_MetaM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownConstant___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDelayedAssigned___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main(lean_object*);
lean_object* l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_savingCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore(lean_object*);
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___closed__2;
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_7__savingCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_HasBeq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1;
lean_object* l_Lean_Meta_mkSynthPendingRef___closed__1;
lean_object* l_Lean_Meta_setMVarKind___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___rarg___closed__2;
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDelayedAssigned___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_approxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_renameMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_mkIsExprDefEqAuxRef___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances(lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_approxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1;
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_map1MetaM(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_monadLiftRefl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkValueTypeClosure(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_modifyMCtx___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftMetaM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_17__forallTelescopeImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_modifyMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_whnf(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addTraceContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_hasEval(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_State_inhabited___closed__2;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2(lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1;
lean_object* l_Lean_Meta_Lean_MonadError___closed__2;
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_inhabited___closed__4;
lean_object* l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_modifyMCtx___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*);
lean_object* l_Lean_Meta_getLCtx___rarg___closed__1;
lean_object* l_Lean_Meta_whnf___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_approxDefEq(lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls(lean_object*);
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_inhabited___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2;
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*);
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___rarg(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1;
lean_object* l_Lean_Meta_throwUnknownConstant(lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*);
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2;
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_30__approxDefEqImpl(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl(lean_object*);
extern lean_object* l_ReaderT_MonadLift___closed__1;
lean_object* l_Lean_Meta_ParamInfo_inhabited;
lean_object* l_Lean_Meta_getLCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1(lean_object*);
lean_object* l_Lean_Meta_getLCtx___rarg(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_16__isClassImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimMVarDeps___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ReaderT_monadError___rarg(lean_object*);
lean_object* l_Lean_Meta_modifyMCtx(lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___closed__6;
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___closed__1;
lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthPendingRef;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1;
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_Lean_SimpleMonadTracerAdapter;
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstanceImpl(lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAuxRef;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_28__withMVarContextImpl(lean_object*);
lean_object* l_Lean_Meta_withLCtx(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReducible___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_fullApproxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency(lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_inhabited___closed__3;
lean_object* l_Lean_Meta_getTransparency___rarg___closed__1;
lean_object* l_Lean_Meta_getParamNames___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg___closed__4;
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_State_inhabited___closed__5;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_restoreSynthInstanceCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5(lean_object*);
lean_object* l_Lean_Meta_mkInferTypeRef(lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDelayedAssigned(lean_object*);
lean_object* l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl(lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1___closed__3;
lean_object* l_Lean_Meta_getMVarDecl(lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___rarg(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency(lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___closed__5;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*);
lean_object* l_Lean_Meta_MonadIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_22__withNewFVar(lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f___rarg(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Meta_forallMetaTelescope___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl(lean_object*);
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx___rarg___closed__3;
lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency___rarg___closed__2;
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_22__withNewFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_26__withNewMCtxDepthImpl(lean_object*);
lean_object* l_Lean_Meta_withConfig(lean_object*);
lean_object* l_Lean_Meta_inferType___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2;
lean_object* l_Lean_Meta_setInlineAttribute___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___closed__3;
lean_object* l_Lean_Meta_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute___rarg___closed__1;
lean_object* l_Lean_Meta_mkFreshTypeMVar(lean_object*);
lean_object* l_Lean_EnumAttributes_setValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___boxed(lean_object**);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*);
lean_object* l_Lean_Meta_mkWHNFRef___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1;
lean_object* l_Lean_Meta_normalizeLevel___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*);
lean_object* l_Lean_Meta_whnfForall___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapterLift___at_Lean_StateRefT_tracer___spec__1___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_15__isClassExpensive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDelayedAssigned___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_getConfig___rarg___closed__1;
lean_object* l_Lean_Meta_getParamNames(lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapterLift___at_Lean_ReaderT_tracer___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*);
lean_object* l_Lean_Meta_whnfD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkInferTypeRef___closed__1;
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*);
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance(lean_object*);
lean_object* l_Lean_Meta_mkWHNFRef(lean_object*);
lean_object* l_Lean_Meta_withReducible(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx(lean_object*);
lean_object* l_Lean_Meta_withMCtx(lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4;
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1;
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7;
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter;
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2;
lean_object* l_Lean_Meta_shouldReduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___rarg___closed__2;
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1;
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Meta_mkFreshTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Meta_mkSynthPendingRef___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l___private_Lean_Meta_Basic_24__withLetDeclImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*);
lean_object* l_Lean_Meta_Lean_MonadError___closed__1;
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadControlRefl___rarg(lean_object*);
lean_object* _init_l_Lean_Meta_ParamInfo_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Meta_ParamInfo_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ParamInfo_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_InfoCacheKey_Inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = l_Lean_Expr_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_InfoCacheKey_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InfoCacheKey_Inhabited___closed__1;
return x_1;
}
}
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
size_t x_2; 
x_2 = 11;
return x_2;
}
else
{
lean_object* x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_usize_of_nat(x_3);
x_5 = 13;
x_6 = lean_usize_mix_hash(x_4, x_5);
return x_6;
}
}
}
size_t l_Lean_Meta_InfoCacheKey_Hashable(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_6 = l_Lean_Expr_hash(x_3);
x_7 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_4);
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
return x_9;
}
}
lean_object* l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_InfoCacheKey_Hashable___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_InfoCacheKey_Hashable(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
uint8_t l_Lean_Meta_InfoCacheKey_HasBeq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Meta_TransparencyMode_beq(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_11; 
x_11 = lean_expr_eqv(x_4, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_eqv(x_4, x_7);
return x_18;
}
}
}
}
}
}
lean_object* l_Lean_Meta_InfoCacheKey_HasBeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_InfoCacheKey_HasBeq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___rarg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1;
return x_1;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___rarg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_HasBeq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_Hashable___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___rarg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1;
x_2 = l_Lean_Meta_State_inhabited___closed__3;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MetavarContext_Inhabited___closed__1;
x_2 = l_Lean_Meta_State_inhabited___closed__4;
x_3 = l_Std_PersistentArray_empty___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_State_inhabited___closed__5;
return x_1;
}
}
lean_object* l_Lean_Meta_MonadIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_apply_1(x_1, x_6);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_io_error_to_string(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_io_error_to_string(x_19);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_MonadIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MonadIO___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MonadIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MonadIO___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_inhabited___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MetaM_inhabited(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_addTraceContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
}
lean_object* l_Lean_Meta_addTraceContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_addTraceContext(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_addTraceContext(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 3);
x_11 = l_Lean_replaceRef(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 3, x_11);
x_12 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_17 = l_Lean_replaceRef(x_2, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_apply_5(x_3, x_4, x_5, x_18, x_7, x_8);
return x_19;
}
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Lean_MonadError;
x_2 = l_Lean_ReaderT_monadError___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Lean_MonadError___closed__1;
x_2 = l_Lean_ReaderT_monadError___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Lean_MonadError___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Lean_MonadError___lambda__2___boxed), 7, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Lean_MonadError___lambda__3___boxed), 8, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Meta_Lean_MonadError___closed__2;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = l_Lean_Meta_Lean_MonadError___closed__3;
x_7 = l_Lean_Meta_Lean_MonadError___closed__4;
x_8 = l_Lean_Meta_Lean_MonadError___closed__5;
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Meta_Lean_MonadError___closed__3;
x_11 = l_Lean_Meta_Lean_MonadError___closed__4;
x_12 = l_Lean_Meta_Lean_MonadError___closed__5;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
return x_13;
}
}
}
lean_object* _init_l_Lean_Meta_Lean_MonadError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Lean_MonadError___closed__6;
return x_1;
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Lean_MonadError___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Lean_MonadError___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_Lean_MonadError___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Lean_MonadError___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_8, 2, x_12);
x_13 = lean_st_ref_set(x_5, x_8, x_9);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_st_ref_set(x_5, x_24, x_9);
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
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Lean_SimpleMonadTracerAdapter;
x_2 = l_Lean_simpleMonadTracerAdapterLift___at_Lean_StateRefT_tracer___spec__1___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3;
x_2 = l_Lean_simpleMonadTracerAdapterLift___at_Lean_ReaderT_tracer___spec__1___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_addTraceContext___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2;
x_7 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5;
x_8 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6;
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2;
x_11 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5;
x_12 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_12);
return x_13;
}
}
}
lean_object* _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7;
return x_1;
}
}
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_mk_ref(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_apply_5(x_1, x_2, x_8, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_1);
lean_ctor_set_uint8(x_3, 4, x_1);
lean_ctor_set_uint8(x_3, 5, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_MetaM_run_x27___rarg___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MetavarContext_Inhabited___closed__1;
x_2 = l_Lean_Meta_State_inhabited___closed__4;
x_3 = l_Std_PersistentArray_empty___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_9);
x_12 = lean_apply_5(x_1, x_11, x_9, x_4, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_14);
lean_dec(x_9);
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
else
{
uint8_t x_20; 
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_MetaM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MetaM_run_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MetaM_run_x27___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_mk_ref(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_mk_ref(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
x_13 = lean_apply_5(x_1, x_4, x_11, x_2, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_8);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_13, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l_Lean_MessageData_formatAux___main(x_33, x_32);
x_35 = l_Lean_Options_empty;
x_36 = l_Lean_Format_pretty(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_13, 0, x_37);
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_dec(x_13);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_box(0);
x_41 = l_Lean_MessageData_formatAux___main(x_40, x_39);
x_42 = l_Lean_Options_empty;
x_43 = l_Lean_Format_pretty(x_41, x_42);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_13, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Nat_repr(x_48);
x_50 = l_Lean_InternalExceptionId_toString___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_13, 0, x_52);
return x_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_dec(x_13);
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
lean_dec(x_29);
x_55 = l_Nat_repr(x_54);
x_56 = l_Lean_InternalExceptionId_toString___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
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
lean_object* _init_l_Lean_Meta_hasEval___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
x_2 = l_Std_PersistentArray_empty___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_hasEval___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_MetaM_run_x27___rarg___closed__1;
x_2 = l_Lean_Meta_hasEval___rarg___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_hasEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = l_Lean_getMaxRecDepth(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_box(0);
lean_inc(x_3);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_Lean_NameGenerator_Inhabited___closed__3;
x_28 = l_Lean_TraceState_Inhabited___closed__1;
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_st_mk_ref(x_29, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_34 = lean_st_mk_ref(x_33, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_hasEval___rarg___closed__2;
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_35);
x_38 = lean_apply_5(x_4, x_37, x_35, x_26, x_31, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_35, x_40);
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(x_26, x_31, x_42);
lean_dec(x_26);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_31, x_44);
lean_dec(x_31);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_apply_5(x_1, x_48, x_3, x_39, x_50, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_7 = x_52;
x_8 = x_53;
goto block_22;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_dec(x_38);
x_56 = l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(x_26, x_31, x_55);
lean_dec(x_31);
lean_dec(x_26);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_7 = x_54;
x_8 = x_57;
goto block_22;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_7 = x_58;
x_8 = x_59;
goto block_22;
}
}
block_22:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Lean_MessageData_formatAux___main(x_10, x_9);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Nat_repr(x_16);
x_18 = l_Lean_InternalExceptionId_toString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_hasEval___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_hasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Meta_hasEval___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isDefEqStuckExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
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
lean_object* l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_getLCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l_Lean_Meta_getLCtx___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getLCtx___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLCtx___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getLCtx___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getLCtx___rarg___closed__1;
x_2 = l_Lean_Meta_getLCtx___rarg___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getLCtx___rarg___closed__3;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_read___at_Lean_Meta_getLCtx___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_getLCtx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLCtx___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_getLocalInstances___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalInstances___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getLocalInstances___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getLCtx___rarg___closed__1;
x_2 = l_Lean_Meta_getLocalInstances___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLocalInstances___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getLocalInstances___rarg___closed__2;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLocalInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalInstances___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalInstances___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLocalInstances___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getConfig___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l_Lean_Meta_getConfig___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConfig___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getConfig___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getLCtx___rarg___closed__1;
x_2 = l_Lean_Meta_getConfig___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getConfig___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getConfig___rarg___closed__2;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getConfig___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getConfig___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getConfig___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_getMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l_Lean_Meta_getMCtx___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getMCtx___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getMCtx___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_getMCtx___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getMCtx___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getMCtx___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getMCtx___rarg___closed__2;
x_2 = l_Lean_Meta_getMCtx___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getMCtx___rarg___closed__4;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_StateRefT_x27_get___at_Lean_Meta_getMCtx___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getMCtx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMCtx___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_setMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_1);
x_11 = lean_st_ref_set(x_2, x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
lean_object* l_Lean_Meta_setMCtx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_setMCtx___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_setMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_setMCtx___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_setMCtx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_setMCtx___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_modifyMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_7, 0, x_11);
x_12 = lean_st_ref_set(x_2, x_7, x_8);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_22 = lean_apply_1(x_1, x_19);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_st_ref_set(x_2, x_23, x_8);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
lean_object* l_Lean_Meta_modifyMCtx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_modifyMCtx___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_modifyMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_modifyMCtx___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_modifyMCtx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_modifyMCtx___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_Meta_addTraceContext(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_mkWHNFRef___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf implementation was not set");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkWHNFRef___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkWHNFRef___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_mkWHNFRef___lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_mkWHNFRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkWHNFRef___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkWHNFRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkWHNFRef___closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_mkWHNFRef___spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_mkWHNFRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkWHNFRef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferType implementation was not set");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_mkInferTypeRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkInferTypeRef___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkInferTypeRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkInferTypeRef___closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_mkWHNFRef___spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkInferTypeRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkInferTypeRef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_mkIsExprDefEqAuxRef___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq implementation was not set");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3;
x_9 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_mkIsExprDefEqAuxRef___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_IO_mkRef___at_Lean_Meta_mkSynthPendingRef___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkSynthPendingRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l_Lean_Meta_mkSynthPendingRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkSynthPendingRef___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkSynthPendingRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkSynthPendingRef___closed__1;
x_3 = l_IO_mkRef___at_Lean_Meta_mkSynthPendingRef___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkSynthPendingRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkSynthPendingRef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_whnf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_whnf___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_2, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_5, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_ctor_set(x_5, 1, x_18);
x_19 = l_Lean_Meta_whnfRef;
x_20 = lean_st_ref_get(x_19, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_3, x_4, x_5, x_6, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_whnfRef;
x_28 = lean_st_ref_get(x_27, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_3, x_4, x_26, x_6, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* _init_l_Lean_Meta_whnf___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___rarg___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_whnf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_whnf___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_whnf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnf___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_whnf___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_whnf___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnf___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfForall___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isForall(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_3);
return x_10;
}
}
}
lean_object* l_Lean_Meta_whnfForall___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf___rarg(x_1, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_whnfForall___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_whnfForall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfForall___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_inferType___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_2, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_5, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_ctor_set(x_5, 1, x_18);
x_19 = l_Lean_Meta_inferTypeRef;
x_20 = lean_st_ref_get(x_19, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_3, x_4, x_5, x_6, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_inferTypeRef;
x_28 = lean_st_ref_get(x_27, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_3, x_4, x_26, x_6, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_inferType___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_whnf___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_inferType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_inferType___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_inferType___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_9, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_5, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_9, x_18);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_19);
x_20 = l_Lean_Meta_isExprDefEqAuxRef;
x_21 = lean_st_ref_get(x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_7(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
x_28 = l_Lean_Meta_isExprDefEqAuxRef;
x_29 = lean_st_ref_get(x_28, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_apply_7(x_30, x_1, x_2, x_3, x_4, x_27, x_6, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_34 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_33, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_synthPending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_synthPendingRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_synthPendingRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_1);
x_17 = lean_metavar_ctx_mk_decl(x_16, x_1, x_6, x_2, x_3, x_4, x_5);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_8, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Lean_mkMVar(x_1);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_mkMVar(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_1);
x_28 = lean_metavar_ctx_mk_decl(x_25, x_1, x_6, x_2, x_3, x_4, x_5);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_st_ref_set(x_8, x_29, x_14);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = l_Lean_mkMVar(x_1);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
lean_object* l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
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
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_5);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_st_ref_set(x_1, x_25, x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
lean_inc(x_31);
lean_inc(x_30);
x_32 = lean_name_mk_numeral(x_30, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_31, x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_st_ref_take(x_1, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 3, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_40);
x_43 = lean_st_ref_set(x_1, x_42, x_38);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_44);
return x_46;
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
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(x_6, x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* _init_l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1___boxed), 11, 5);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_6);
x_9 = l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVarAt___rarg___boxed), 6, 0);
return x_2;
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
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_mkFreshExprMVarAt___rarg___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkFreshExprMVarAt___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_1);
x_12 = l_Lean_MetavarContext_addLevelMVarDecl(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l_Lean_mkLevelMVar(x_1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_mkLevelMVar(x_1);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_1);
x_23 = l_Lean_MetavarContext_addLevelMVarDecl(x_20, x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
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
x_28 = l_Lean_mkLevelMVar(x_1);
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
lean_object* _init_l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1;
x_2 = l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVar___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkFreshLevelMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3(x_10, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_6);
x_13 = l_Lean_MetavarContext_addLevelMVarDecl(x_12, x_6);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_st_ref_set(x_1, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Lean_mkLevelMVar(x_6);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_mkLevelMVar(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_6);
x_24 = l_Lean_MetavarContext_addLevelMVarDecl(x_21, x_6);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = l_Lean_mkLevelMVar(x_6);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkSort(x_10);
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(x_12, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l___private_Lean_Meta_Basic_3__mkFreshExprMVarCore(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___boxed), 8, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Meta_mkFreshExprMVar___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Meta_mkFreshTypeMVar___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_mkSort(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_10, x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* _init_l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshTypeMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Meta_mkFreshTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Meta_mkFreshTypeMVar___spec__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_mkFreshTypeMVar___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshTypeMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_mkFreshTypeMVar___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(x_1, x_5, x_12, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_5);
x_8 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Basic_2__mkFreshExprMVarAtCore(x_1, x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_6, x_7, x_8, x_9);
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
x_17 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___at_Lean_Meta_mkFreshExprMVarWithIdImpl___spec__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_mkFreshExprMVarWithIdImpl(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVarWithIdImpl___boxed), 9, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVarWithId___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_mkFreshExprMVarWithId___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_shouldReduceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_6, 5);
x_8 = 0;
x_9 = l_Lean_Meta_TransparencyMode_beq(x_7, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
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
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_7, 5);
x_9 = 2;
x_10 = l_Lean_Meta_TransparencyMode_beq(x_8, x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
lean_object* _init_l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getLCtx___rarg___closed__1;
x_2 = l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_shouldReduceReducibleOnly___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_shouldReduceReducibleOnly___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getTransparency___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_7, 5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* _init_l_Lean_Meta_getTransparency___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getTransparency___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getTransparency___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getLCtx___rarg___closed__1;
x_2 = l_Lean_Meta_getTransparency___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getTransparency___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getTransparency___rarg___closed__2;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getTransparency___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getTransparency___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getTransparency___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_isReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_isReducible(x_10, x_1);
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
x_16 = l_Lean_isReducible(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
lean_object* l_Lean_Meta_isReducible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReducible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown metavariable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = lean_metavar_ctx_find_decl(x_2, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_mkMVar(x_1);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
lean_object* _init_l_Lean_Meta_getMVarDecl___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_getMVarDecl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getMVarDecl___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_setMVarKind___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_MetavarContext_setMVarKind(x_11, x_1, x_2);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = l_Lean_MetavarContext_setMVarKind(x_20, x_1, x_2);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
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
lean_object* l_Lean_Meta_setMVarKind___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_setMVarKind___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_setMVarKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_setMVarKind___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_setMVarKind___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Meta_setMVarKind___rarg___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_setMVarKind___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Meta_setMVarKind___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_11 = lean_metavar_ctx_find_decl(x_9, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_7);
x_12 = l_Lean_mkMVar(x_1);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_17, x_2, x_3, x_4, x_5, x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_1);
x_22 = lean_metavar_ctx_find_decl(x_20, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = l_Lean_mkMVar(x_1);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_1, 3);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
}
}
lean_object* _init_l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyExprMVar___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyExprMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_30; lean_object* x_31; 
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_31 = lean_box(x_30);
if (lean_obj_tag(x_31) == 2)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_31);
x_35 = lean_box(0);
x_7 = x_35;
goto block_29;
}
block_29:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe metavariable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_MetavarContext_findLevelDepth_x3f(x_2, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_9 = l_Lean_mkLevelMVar(x_1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isReadOnlyLevelMVar___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_renameMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_MetavarContext_renameMVar(x_11, x_1, x_2);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = l_Lean_MetavarContext_renameMVar(x_20, x_1, x_2);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
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
lean_object* l_Lean_Meta_renameMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_renameMVar___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_renameMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_renameMVar___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_renameMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_renameMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_metavar_ctx_is_expr_assigned(x_2, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isExprMVarAssigned___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprMVarAssigned___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_metavar_ctx_get_expr_assignment(x_2, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getExprMVarAssignment_x3f___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_assignExprMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_MetavarContext_assignExpr(x_11, x_1, x_2);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = l_Lean_MetavarContext_assignExpr(x_20, x_1, x_2);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
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
lean_object* l_Lean_Meta_assignExprMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_assignExprMVar___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_assignExprMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_assignExprMVar___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_assignExprMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_assignExprMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_isDelayedAssigned___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_metavar_ctx_is_delayed_assigned(x_2, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_isDelayedAssigned___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_isDelayedAssigned___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_isDelayedAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isDelayedAssigned___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isDelayedAssigned___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isDelayedAssigned___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_metavar_ctx_get_delayed_assignment(x_2, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getDelayedAssignment_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getDelayedAssignment_x3f___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_MetavarContext_hasAssignableMVar___main(x_2, x_1);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_hasAssignableMVar___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_getMVarDecl___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_hasAssignableMVar___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_hasAssignableMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown free variable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownFVar___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownFVar___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
x_9 = l_Lean_Meta_throwUnknownFVar___rarg___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_Meta_getLocalDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
lean_object* l_Lean_Meta_getLocalDecl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_getLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getLocalDecl___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_11 = lean_local_ctx_find(x_9, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_free_object(x_7);
x_12 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_1);
x_16 = lean_local_ctx_find(x_14, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_2, x_3, x_4, x_5, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getFVarLocalDecl___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getFVarLocalDecl___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateMVars___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_MetavarContext_instantiateMVars(x_10, x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_13);
x_14 = lean_st_ref_set(x_2, x_7, x_8);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_22 = l_Lean_MetavarContext_instantiateMVars(x_19, x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_st_ref_set(x_2, x_25, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___rarg___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_instantiateMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___rarg), 2, 0);
return x_2;
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_instantiateMVars___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_instantiateMVars___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasMVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_MetavarContext_instantiateMVars(x_13, x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_3, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_25 = l_Lean_MetavarContext_instantiateMVars(x_22, x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_st_ref_set(x_3, x_28, x_11);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_5);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_5);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_box(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed), 6, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2___boxed), 10, 4);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_15);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_apply_2(x_1, lean_box(0), x_20);
return x_21;
}
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLocalDeclMVars___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_instantiateLocalDeclMVars___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
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
x_12 = lean_st_ref_set(x_3, x_8, x_9);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_3, x_21, x_9);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create binder due to failure when reverting variable dependencies");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_2, x_3, x_4, x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_HashMap_inhabited___closed__1;
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_apply_2(x_1, x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_st_ref_take(x_5, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
lean_ctor_set(x_25, 1, x_23);
x_29 = lean_st_ref_set(x_5, x_25, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_22, x_2, x_3, x_4, x_5, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_st_ref_set(x_5, x_38, x_26);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_22, x_2, x_3, x_4, x_5, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_46, x_2, x_3, x_4, x_5, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_take(x_5, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_51, 1);
lean_dec(x_54);
lean_ctor_set(x_51, 1, x_47);
x_55 = lean_st_ref_set(x_5, x_51, x_52);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_58 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_57, x_2, x_3, x_4, x_5, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_st_ref_set(x_5, x_61, x_52);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_65 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_64, x_2, x_3, x_4, x_5, x_63);
return x_65;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_mkForallFVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_mkForall), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed), 6, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_mkForallFVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_mkLambda), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed), 6, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkLetFVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_mkLambdaFVars___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkLetFVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForallUsedOnly___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_mkForallUsedOnly), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed), 6, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_mkForallUsedOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallUsedOnly___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_elimMVarDeps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_MetavarContext_elimMVarDeps___boxed), 5, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_elimMVarDeps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_elimMVarDeps___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_elimMVarDeps___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Meta_elimMVarDeps___rarg(x_1, x_2, x_3, x_5);
return x_6;
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get_uint8(x_10, 0);
x_22 = lean_ctor_get_uint8(x_10, 1);
x_23 = lean_ctor_get_uint8(x_10, 2);
x_24 = lean_ctor_get_uint8(x_10, 3);
x_25 = lean_ctor_get_uint8(x_10, 4);
lean_dec(x_10);
x_26 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_26, 0, x_21);
lean_ctor_set_uint8(x_26, 1, x_22);
lean_ctor_set_uint8(x_26, 2, x_23);
lean_ctor_set_uint8(x_26, 3, x_24);
lean_ctor_set_uint8(x_26, 4, x_25);
lean_ctor_set_uint8(x_26, 5, x_1);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_39 = lean_ctor_get_uint8(x_36, 0);
x_40 = lean_ctor_get_uint8(x_36, 1);
x_41 = lean_ctor_get_uint8(x_36, 2);
x_42 = lean_ctor_get_uint8(x_36, 3);
x_43 = lean_ctor_get_uint8(x_36, 4);
if (lean_is_exclusive(x_36)) {
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 0, 6);
} else {
 x_45 = x_44;
}
lean_ctor_set_uint8(x_45, 0, x_39);
lean_ctor_set_uint8(x_45, 1, x_40);
lean_ctor_set_uint8(x_45, 2, x_41);
lean_ctor_set_uint8(x_45, 3, x_42);
lean_ctor_set_uint8(x_45, 4, x_43);
lean_ctor_set_uint8(x_45, 5, x_1);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_38);
x_47 = lean_apply_7(x_3, lean_box(0), x_2, x_46, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
lean_dec(x_9);
x_26 = 2;
x_27 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_27, 0, x_21);
lean_ctor_set_uint8(x_27, 1, x_22);
lean_ctor_set_uint8(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, 3, x_24);
lean_ctor_set_uint8(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, 5, x_26);
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
x_40 = lean_ctor_get_uint8(x_37, 0);
x_41 = lean_ctor_get_uint8(x_37, 1);
x_42 = lean_ctor_get_uint8(x_37, 2);
x_43 = lean_ctor_get_uint8(x_37, 3);
x_44 = lean_ctor_get_uint8(x_37, 4);
if (lean_is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = 2;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 6);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_40);
lean_ctor_set_uint8(x_47, 1, x_41);
lean_ctor_set_uint8(x_47, 2, x_42);
lean_ctor_set_uint8(x_47, 3, x_43);
lean_ctor_set_uint8(x_47, 4, x_44);
lean_ctor_set_uint8(x_47, 5, x_46);
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
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_16 = lean_ctor_get_uint8(x_10, 0);
x_17 = lean_ctor_get_uint8(x_10, 1);
x_18 = lean_ctor_get_uint8(x_10, 2);
x_19 = lean_ctor_get_uint8(x_10, 3);
x_20 = lean_ctor_get_uint8(x_10, 4);
x_21 = lean_ctor_get_uint8(x_10, 5);
lean_dec(x_10);
x_22 = l_Lean_Meta_TransparencyMode_lt(x_21, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_23, 0, x_16);
lean_ctor_set_uint8(x_23, 1, x_17);
lean_ctor_set_uint8(x_23, 2, x_18);
lean_ctor_set_uint8(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, 4, x_20);
lean_ctor_set_uint8(x_23, 5, x_21);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_25, 0, x_16);
lean_ctor_set_uint8(x_25, 1, x_17);
lean_ctor_set_uint8(x_25, 2, x_18);
lean_ctor_set_uint8(x_25, 3, x_19);
lean_ctor_set_uint8(x_25, 4, x_20);
lean_ctor_set_uint8(x_25, 5, x_1);
lean_ctor_set(x_4, 0, x_25);
x_26 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_30 = lean_ctor_get_uint8(x_27, 0);
x_31 = lean_ctor_get_uint8(x_27, 1);
x_32 = lean_ctor_get_uint8(x_27, 2);
x_33 = lean_ctor_get_uint8(x_27, 3);
x_34 = lean_ctor_get_uint8(x_27, 4);
x_35 = lean_ctor_get_uint8(x_27, 5);
if (lean_is_exclusive(x_27)) {
 x_36 = x_27;
} else {
 lean_dec_ref(x_27);
 x_36 = lean_box(0);
}
x_37 = l_Lean_Meta_TransparencyMode_lt(x_35, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 0, 6);
} else {
 x_38 = x_36;
}
lean_ctor_set_uint8(x_38, 0, x_30);
lean_ctor_set_uint8(x_38, 1, x_31);
lean_ctor_set_uint8(x_38, 2, x_32);
lean_ctor_set_uint8(x_38, 3, x_33);
lean_ctor_set_uint8(x_38, 4, x_34);
lean_ctor_set_uint8(x_38, 5, x_35);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
x_40 = lean_apply_7(x_3, lean_box(0), x_2, x_39, x_5, x_6, x_7, x_8);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(0, 0, 6);
} else {
 x_41 = x_36;
}
lean_ctor_set_uint8(x_41, 0, x_30);
lean_ctor_set_uint8(x_41, 1, x_31);
lean_ctor_set_uint8(x_41, 2, x_32);
lean_ctor_set_uint8(x_41, 3, x_33);
lean_ctor_set_uint8(x_41, 4, x_34);
lean_ctor_set_uint8(x_41, 5, x_1);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
x_43 = lean_apply_7(x_3, lean_box(0), x_2, x_42, x_5, x_6, x_7, x_8);
return x_43;
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
lean_object* l_Lean_Meta_throwUnknownConstant___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_throwUnknownConstant(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwUnknownConstant___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_throwUnknownConstant___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwUnknownConstant___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_6, 5);
x_8 = 2;
x_9 = l_Lean_Meta_TransparencyMode_beq(x_7, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_getConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_13; 
lean_free_object(x_7);
x_13 = l_Lean_Meta_throwUnknownConstant___rarg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 1:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_14);
lean_free_object(x_7);
x_15 = l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(x_2, x_3, x_4, x_5, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Meta_isReducible(x_1, x_2, x_3, x_4, x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_1);
x_36 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
lean_ctor_set(x_36, 0, x_12);
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
default: 
{
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = lean_environment_find(x_51, x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Meta_throwUnknownConstant___rarg(x_1, x_2, x_3, x_4, x_5, x_50);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
switch (lean_obj_tag(x_54)) {
case 1:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_54);
x_55 = l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(x_2, x_3, x_4, x_5, x_50);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l_Lean_Meta_isReducible(x_1, x_2, x_3, x_4, x_5, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
case 2:
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_54);
lean_dec(x_1);
x_72 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_50);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_52);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_52);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
default: 
{
lean_object* x_82; 
lean_dec(x_54);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_52);
lean_ctor_set(x_82, 1, x_50);
return x_82;
}
}
}
}
}
}
lean_object* l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getConst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getConst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 1:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_13);
lean_free_object(x_7);
x_14 = l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(x_2, x_3, x_4, x_5, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Meta_isReducible(x_1, x_2, x_3, x_4, x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
case 2:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_1);
x_35 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_12);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_35, 0, x_40);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
lean_ctor_set(x_35, 0, x_12);
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
default: 
{
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_7);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_1);
x_51 = lean_environment_find(x_50, x_1);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
switch (lean_obj_tag(x_53)) {
case 1:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_54 = l_Lean_Meta_shouldReduceReducibleOnly___at_Lean_Meta_getConst_x3f___spec__1(x_2, x_3, x_4, x_5, x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_Lean_Meta_isReducible(x_1, x_2, x_3, x_4, x_5, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
case 2:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_53);
lean_dec(x_1);
x_71 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_49);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_51);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_51);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
default: 
{
lean_object* x_81; 
lean_dec(x_53);
lean_dec(x_1);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_51);
lean_ctor_set(x_81, 1, x_49);
return x_81;
}
}
}
}
}
}
lean_object* l_Lean_Meta_getConstNoEx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getConstNoEx_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_7__savingCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_10);
x_19 = lean_st_ref_set(x_3, x_15, x_16);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_st_ref_set(x_3, x_26, x_16);
lean_dec(x_3);
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
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_st_ref_take(x_3, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_34, 1);
lean_dec(x_37);
lean_ctor_set(x_34, 1, x_10);
x_38 = lean_st_ref_set(x_3, x_34, x_35);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_31);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_st_ref_set(x_3, x_45, x_35);
lean_dec(x_3);
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
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_7__savingCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_7__savingCacheImpl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_11);
x_20 = lean_st_ref_set(x_4, x_16, x_17);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_st_ref_set(x_4, x_27, x_17);
lean_dec(x_4);
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
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_st_ref_take(x_4, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_dec(x_38);
lean_ctor_set(x_35, 1, x_11);
x_39 = lean_st_ref_set(x_4, x_35, x_36);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_32);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_st_ref_set(x_4, x_46, x_36);
lean_dec(x_4);
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
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_48);
return x_50;
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
lean_object* l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_Meta_getConst_x3f(x_1, x_2, x_3, x_4, x_5, x_10);
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
x_36 = l_Lean_Meta_getConst_x3f(x_1, x_2, x_3, x_4, x_5, x_33);
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
lean_object* l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_metavar_ctx_get_expr_assignment(x_9, x_1);
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
x_13 = lean_metavar_ctx_get_expr_assignment(x_11, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_inhabited___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
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
x_20 = l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f(x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Expr_getAppFn___main(x_21);
lean_dec(x_21);
switch (lean_obj_tag(x_22)) {
case 4:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Basic_8__isClassQuickConst_x3f(x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
case 12:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_37 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_38 = l_unreachable_x21___rarg(x_37);
x_39 = lean_apply_5(x_38, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
}
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_12, 2);
lean_dec(x_17);
x_18 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2;
lean_ctor_set(x_12, 2, x_18);
x_19 = lean_st_ref_set(x_1, x_11, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_28 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2;
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_11, 1, x_29);
x_30 = lean_st_ref_set(x_1, x_11, x_13);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_12, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_12, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_40 = x_12;
} else {
 lean_dec_ref(x_12);
 x_40 = lean_box(0);
}
x_41 = l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2;
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_st_ref_set(x_1, x_43, x_13);
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
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_45);
return x_47;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 2);
lean_dec(x_14);
lean_ctor_set(x_9, 2, x_1);
x_15 = lean_st_ref_set(x_3, x_8, x_10);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 3);
x_25 = lean_ctor_get(x_9, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_1);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_8, 1, x_26);
x_27 = lean_st_ref_set(x_3, x_8, x_10);
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
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 4);
lean_inc(x_37);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 x_38 = x_9;
} else {
 lean_dec_ref(x_9);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 5, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_1);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_33);
x_41 = lean_st_ref_set(x_3, x_40, x_10);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
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
lean_object* l___private_Lean_Meta_Basic_10__resettingSynthInstanceCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_Basic_10__resettingSynthInstanceCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_10__resettingSynthInstanceCacheImpl___rarg), 6, 0);
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
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstanceImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_apply_5(x_3, x_17, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_restoreSynthInstanceCache(x_10, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_Meta_restoreSynthInstanceCache(x_10, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstanceImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_11__withNewLocalInstanceImpl___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_apply_7(x_4, lean_box(0), x_3, x_18, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_restoreSynthInstanceCache(x_11, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_restoreSynthInstanceCache(x_11, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
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
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_6);
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
lean_object* _init_l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_monadLiftRefl), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_apply_5(x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
x_15 = l_Lean_Meta_getFVarLocalDecl___rarg(x_14, x_13);
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
x_19 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_20 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_3 = x_24;
x_9 = x_22;
goto _start;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 2);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_13);
x_37 = lean_array_push(x_35, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_2, x_29, x_4, x_38, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_restoreSynthInstanceCache(x_31, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_Lean_Meta_restoreSynthInstanceCache(x_31, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
default: 
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_dec(x_20);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = lean_apply_6(x_1, x_19, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_13);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_3, x_58);
lean_dec(x_3);
x_3 = x_59;
x_9 = x_57;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_3, x_63);
lean_dec(x_3);
x_65 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_13);
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_72);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_74 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_2, x_64, x_4, x_73, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_restoreSynthInstanceCache(x_66, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec(x_74);
x_84 = l_Lean_Meta_restoreSynthInstanceCache(x_66, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_55);
if (x_89 == 0)
{
return x_55;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_55, 0);
x_91 = lean_ctor_get(x_55, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_55);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_20);
if (x_93 == 0)
{
return x_20;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_20, 0);
x_95 = lean_ctor_get(x_20, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_20);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_16);
if (x_97 == 0)
{
return x_16;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_16, 0);
x_99 = lean_ctor_get(x_16, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_16);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isForall(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_16 = lean_apply_7(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(x_4, x_5, x_6, x_1, x_7, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_MonadLift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadNameGenerator;
x_2 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4;
x_3 = l_Lean_monadNameGeneratorLift___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5;
x_2 = l_ReaderT_MonadLift___closed__1;
x_3 = l_Lean_monadNameGeneratorLift___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
if (lean_obj_tag(x_8) == 7)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_8, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_45 = lean_array_get_size(x_6);
x_46 = lean_expr_instantiate_rev_range(x_42, x_7, x_45, x_6);
lean_dec(x_45);
lean_dec(x_42);
x_47 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_48 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6;
x_49 = l_Lean_mkFreshId___rarg(x_47, x_48);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_50 = lean_apply_5(x_49, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = (uint8_t)((x_44 << 24) >> 61);
lean_inc(x_51);
x_54 = lean_local_ctx_mk_local_decl(x_5, x_51, x_41, x_46, x_53);
x_55 = l_Lean_mkFVar(x_51);
x_56 = lean_array_push(x_6, x_55);
x_5 = x_54;
x_6 = x_56;
x_8 = x_43;
x_13 = x_52;
goto _start;
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_8, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_8, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_67 = lean_array_get_size(x_6);
x_68 = lean_nat_dec_lt(x_67, x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_3);
x_69 = lean_expr_instantiate_rev_range(x_8, x_7, x_67, x_6);
lean_dec(x_67);
lean_dec(x_8);
lean_inc(x_6);
x_70 = lean_apply_2(x_4, x_6, x_69);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_9, 1);
lean_dec(x_72);
lean_ctor_set(x_9, 1, x_5);
x_73 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_70, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_9, 0);
x_75 = lean_ctor_get(x_9, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_9);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_5);
lean_ctor_set(x_76, 2, x_75);
x_77 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_70, x_76, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_8);
x_78 = lean_expr_instantiate_rev_range(x_63, x_7, x_67, x_6);
lean_dec(x_67);
lean_dec(x_63);
x_79 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_80 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6;
x_81 = l_Lean_mkFreshId___rarg(x_79, x_80);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_82 = lean_apply_5(x_81, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = (uint8_t)((x_65 << 24) >> 61);
lean_inc(x_83);
x_86 = lean_local_ctx_mk_local_decl(x_5, x_83, x_62, x_78, x_85);
x_87 = l_Lean_mkFVar(x_83);
x_88 = lean_array_push(x_6, x_87);
x_5 = x_86;
x_6 = x_88;
x_8 = x_64;
x_13 = x_84;
goto _start;
}
else
{
uint8_t x_90; 
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_14 = x_94;
goto block_40;
}
block_40:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_14);
x_15 = lean_array_get_size(x_6);
x_16 = lean_expr_instantiate_rev_range(x_8, x_7, x_15, x_6);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_5);
if (x_2 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_6);
x_19 = lean_apply_2(x_4, x_6, x_16);
x_20 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
lean_inc(x_16);
x_22 = l_Lean_Meta_whnf___rarg(x_21, x_16);
x_23 = lean_box(x_2);
lean_inc(x_1);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed), 14, 8);
lean_closure_set(x_24, 0, x_4);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_16);
lean_closure_set(x_24, 3, x_1);
lean_closure_set(x_24, 4, x_23);
lean_closure_set(x_24, 5, x_3);
lean_closure_set(x_24, 6, x_5);
lean_closure_set(x_24, 7, x_15);
x_25 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, lean_box(0));
lean_closure_set(x_26, 3, x_22);
lean_closure_set(x_26, 4, x_24);
x_27 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_26, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
lean_inc(x_5);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
if (x_2 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_6);
x_31 = lean_apply_2(x_4, x_6, x_16);
x_32 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_31, x_30, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
lean_inc(x_16);
x_34 = l_Lean_Meta_whnf___rarg(x_33, x_16);
x_35 = lean_box(x_2);
lean_inc(x_1);
lean_inc(x_6);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed), 14, 8);
lean_closure_set(x_36, 0, x_4);
lean_closure_set(x_36, 1, x_6);
lean_closure_set(x_36, 2, x_16);
lean_closure_set(x_36, 3, x_1);
lean_closure_set(x_36, 4, x_35);
lean_closure_set(x_36, 5, x_3);
lean_closure_set(x_36, 6, x_5);
lean_closure_set(x_36, 7, x_15);
x_37 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, lean_box(0));
lean_closure_set(x_38, 2, lean_box(0));
lean_closure_set(x_38, 3, x_34);
lean_closure_set(x_38, 4, x_36);
x_39 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_1, x_6, x_7, x_38, x_30, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_39;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___rarg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
lean_inc(x_2);
x_11 = l_Lean_Meta_whnf___rarg(x_10, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_5(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_isForall(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Array_empty___closed__1;
x_17 = lean_apply_7(x_4, x_16, x_2, x_5, x_6, x_7, x_8, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_18 = l_Lean_Meta_getLCtx___rarg(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_apply_5(x_18, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = l_Array_empty___closed__1;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg(x_1, x_22, x_3, x_4, x_20, x_23, x_24, x_13, x_5, x_6, x_7, x_8, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_whnfRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_whnfRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_fvarId_x21(x_1);
x_8 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_7, x_8);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_12);
x_17 = lean_is_class(x_16, x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_12);
x_23 = lean_is_class(x_22, x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_2, x_3);
x_31 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_30, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_LocalDecl_type(x_32);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_34);
x_35 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_34, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
switch (lean_obj_tag(x_36)) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_30);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
lean_dec(x_3);
x_3 = x_39;
x_8 = x_37;
goto _start;
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_45 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 2);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_30);
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(x_1, x_2, x_44, x_53, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_restoreSynthInstanceCache(x_46, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = l_Lean_Meta_restoreSynthInstanceCache(x_46, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
default: 
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
lean_dec(x_35);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_34, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_30);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_3, x_73);
lean_dec(x_3);
x_3 = x_74;
x_8 = x_72;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_3, x_78);
lean_dec(x_3);
x_80 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_76);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_4, 2);
lean_inc(x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_30);
x_87 = lean_array_push(x_85, x_86);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_87);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_89 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(x_1, x_2, x_79, x_88, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_restoreSynthInstanceCache(x_81, x_4, x_5, x_6, x_7, x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_dec(x_89);
x_99 = l_Lean_Meta_restoreSynthInstanceCache(x_81, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
lean_ctor_set_tag(x_99, 1);
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_70);
if (x_104 == 0)
{
return x_70;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_70, 0);
x_106 = lean_ctor_get(x_70, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_70);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_35);
if (x_108 == 0)
{
return x_35;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_35, 0);
x_110 = lean_ctor_get(x_35, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_35);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_31);
if (x_112 == 0)
{
return x_31;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_31, 0);
x_114 = lean_ctor_get(x_31, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_31);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_11, x_12);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_15);
x_20 = lean_is_class(x_19, x_15);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_15);
x_26 = lean_is_class(x_25, x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_16, 0, x_8);
x_17 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1___boxed), 12, 6);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_7);
x_19 = lean_array_get_size(x_9);
x_20 = lean_nat_dec_lt(x_10, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(x_16, x_18, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
x_22 = lean_array_fget(x_9, x_10);
x_23 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_22, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_26);
x_27 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_26, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_22);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_10, x_30);
lean_dec(x_10);
x_10 = x_31;
x_15 = x_29;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_10, x_35);
lean_dec(x_10);
x_37 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_11, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 2);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_22);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_46 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36, x_45, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_restoreSynthInstanceCache(x_38, x_11, x_12, x_13, x_14, x_48);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = l_Lean_Meta_restoreSynthInstanceCache(x_38, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
default: 
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_dec(x_27);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_62 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_26, x_11, x_12, x_13, x_14, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_22);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_10, x_65);
lean_dec(x_10);
x_10 = x_66;
x_15 = x_64;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_10, x_70);
lean_dec(x_10);
x_72 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_11, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 2);
lean_inc(x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_22);
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_81 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_71, x_80, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_restoreSynthInstanceCache(x_73, x_11, x_12, x_13, x_14, x_83);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_Meta_restoreSynthInstanceCache(x_73, x_11, x_12, x_13, x_14, x_90);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_62);
if (x_96 == 0)
{
return x_62;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_62, 0);
x_98 = lean_ctor_get(x_62, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_62);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_27);
if (x_100 == 0)
{
return x_27;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_27, 0);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_27);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_23);
if (x_104 == 0)
{
return x_23;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_23, 0);
x_106 = lean_ctor_get(x_23, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_23);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_7, x_8);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_12);
x_17 = lean_is_class(x_16, x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_12);
x_23 = lean_is_class(x_22, x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_2, x_3);
x_31 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_30, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_LocalDecl_type(x_32);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_34);
x_35 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_34, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
switch (lean_obj_tag(x_36)) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_30);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
lean_dec(x_3);
x_3 = x_39;
x_8 = x_37;
goto _start;
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_45 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 2);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_30);
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(x_1, x_2, x_44, x_53, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_restoreSynthInstanceCache(x_46, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = l_Lean_Meta_restoreSynthInstanceCache(x_46, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
default: 
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
lean_dec(x_35);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_34, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_30);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_3, x_73);
lean_dec(x_3);
x_3 = x_74;
x_8 = x_72;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_3, x_78);
lean_dec(x_3);
x_80 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_76);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_4, 2);
lean_inc(x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_30);
x_87 = lean_array_push(x_85, x_86);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_87);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_89 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(x_1, x_2, x_79, x_88, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_restoreSynthInstanceCache(x_81, x_4, x_5, x_6, x_7, x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_dec(x_89);
x_99 = l_Lean_Meta_restoreSynthInstanceCache(x_81, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
lean_ctor_set_tag(x_99, 1);
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_70);
if (x_104 == 0)
{
return x_70;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_70, 0);
x_106 = lean_ctor_get(x_70, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_70);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_35);
if (x_108 == 0)
{
return x_35;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_35, 0);
x_110 = lean_ctor_get(x_35, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_35);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_31);
if (x_112 == 0)
{
return x_31;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_31, 0);
x_114 = lean_ctor_get(x_31, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_31);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
if (lean_obj_tag(x_6) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_29 = lean_array_get_size(x_4);
x_30 = lean_expr_instantiate_rev_range(x_26, x_5, x_29, x_4);
lean_dec(x_29);
lean_dec(x_26);
x_31 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = (uint8_t)((x_28 << 24) >> 61);
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_3, x_32, x_25, x_30, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_4, x_36);
x_3 = x_35;
x_4 = x_37;
x_6 = x_27;
x_11 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_4);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_46 = lean_expr_instantiate_rev_range(x_6, x_5, x_44, x_4);
lean_dec(x_44);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_7, 1);
lean_dec(x_48);
lean_ctor_set(x_7, 1, x_3);
x_49 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(x_46, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_51);
x_53 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(x_46, x_4, x_5, x_52, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_46);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_6);
x_54 = lean_expr_instantiate_rev_range(x_40, x_5, x_44, x_4);
lean_dec(x_44);
lean_dec(x_40);
x_55 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = (uint8_t)((x_42 << 24) >> 61);
lean_inc(x_56);
x_59 = lean_local_ctx_mk_local_decl(x_3, x_56, x_39, x_54, x_58);
x_60 = l_Lean_mkFVar(x_56);
x_61 = lean_array_push(x_4, x_60);
x_3 = x_59;
x_4 = x_61;
x_6 = x_41;
x_11 = x_57;
goto _start;
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_12 = x_63;
goto block_24;
}
block_24:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
x_13 = lean_array_get_size(x_4);
x_14 = lean_expr_instantiate_rev_range(x_6, x_5, x_13, x_4);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
if (x_1 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(x_14, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_3);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
if (x_1 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(x_14, x_4, x_5, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_14);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_5);
lean_inc(x_4);
x_23 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_4, x_5, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isForall(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_6, x_11);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_14);
x_19 = lean_is_class(x_18, x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_14);
x_25 = lean_is_class(x_24, x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_6);
x_30 = lean_box(0);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_8);
lean_dec(x_1);
x_31 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 1;
x_35 = l_Array_empty___closed__1;
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(x_34, x_2, x_32, x_35, x_36, x_10, x_3, x_4, x_5, x_6, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = l_Lean_Expr_isForall(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 4)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_get(x_6, x_39);
lean_dec(x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_42);
x_48 = lean_is_class(x_47, x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_49 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_42);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_41);
lean_dec(x_6);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_39);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_55 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_39);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = 1;
x_59 = l_Array_empty___closed__1;
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(x_58, x_2, x_56, x_59, x_60, x_38, x_3, x_4, x_5, x_6, x_57);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
return x_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__1(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
lean_dec(x_9);
x_26 = 2;
x_27 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_27, 0, x_21);
lean_ctor_set_uint8(x_27, 1, x_22);
lean_ctor_set_uint8(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, 3, x_24);
lean_ctor_set_uint8(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, 5, x_26);
lean_ctor_set(x_2, 0, x_27);
x_28 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__1(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_40 = lean_ctor_get_uint8(x_37, 0);
x_41 = lean_ctor_get_uint8(x_37, 1);
x_42 = lean_ctor_get_uint8(x_37, 2);
x_43 = lean_ctor_get_uint8(x_37, 3);
x_44 = lean_ctor_get_uint8(x_37, 4);
if (lean_is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = 2;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 6);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_40);
lean_ctor_set_uint8(x_47, 1, x_41);
lean_ctor_set_uint8(x_47, 2, x_42);
lean_ctor_set_uint8(x_47, 3, x_43);
lean_ctor_set_uint8(x_47, 4, x_44);
lean_ctor_set_uint8(x_47, 5, x_46);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_39);
x_49 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__1(x_1, x_7, x_48, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__6(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_15__isClassExpensive_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_16__isClassImpl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_24 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_1, x_2, x_3, x_4, x_5, x_23);
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
lean_object* l_Lean_Meta_isClass_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_16__isClassImpl_x3f), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isClass_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isClass_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_15__isClassExpensive_x3f), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1;
x_12 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg(x_11, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___boxed), 9, 3);
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
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_expr_instantiate_rev_range(x_4, x_3, x_12, x_2);
lean_dec(x_12);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_apply_7(x_1, x_2, x_13, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_17 = lean_array_fget(x_5, x_6);
x_18 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_6 = x_26;
x_11 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_41 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_31, x_40, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_21, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_6, x_60);
lean_dec(x_6);
x_6 = x_61;
x_11 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_6, x_65);
lean_dec(x_6);
x_67 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_7, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_76 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_66, x_75, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_16 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg(x_1, x_4, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_9);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_box(x_2);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_5);
lean_closure_set(x_19, 2, x_9);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_4);
lean_closure_set(x_19, 6, x_8);
x_20 = lean_array_get_size(x_10);
x_21 = lean_nat_dec_lt(x_11, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(x_17, x_19, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
x_23 = lean_array_fget(x_10, x_11);
x_24 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_23, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_type(x_25);
lean_dec(x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_27, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_23);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_11, x_31);
lean_dec(x_11);
x_11 = x_32;
x_16 = x_30;
goto _start;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_11, x_36);
lean_dec(x_11);
x_38 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_13, x_14, x_15, x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_12, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 2);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_23);
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_47 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37, x_46, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_12, x_13, x_14, x_15, x_49);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_12, x_13, x_14, x_15, x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_63 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_27, x_12, x_13, x_14, x_15, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_11, x_66);
lean_dec(x_11);
x_11 = x_67;
x_16 = x_65;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_11, x_71);
lean_dec(x_11);
x_73 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_13, x_14, x_15, x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_12, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_12, 2);
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_23);
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_80);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_82 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72, x_81, x_13, x_14, x_15, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_12, x_13, x_14, x_15, x_84);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_12, x_13, x_14, x_15, x_91);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set_tag(x_92, 1);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_63);
if (x_97 == 0)
{
return x_63;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_63, 0);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_63);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_28);
if (x_101 == 0)
{
return x_28;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_28, 0);
x_103 = lean_ctor_get(x_28, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_28);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_24);
if (x_105 == 0)
{
return x_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_24, 0);
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_24);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_expr_instantiate_rev_range(x_4, x_3, x_12, x_2);
lean_dec(x_12);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_apply_7(x_1, x_2, x_13, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_17 = lean_array_fget(x_5, x_6);
x_18 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_6 = x_26;
x_11 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_41 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_31, x_40, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_21, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_6, x_60);
lean_dec(x_6);
x_6 = x_61;
x_11 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_6, x_65);
lean_dec(x_6);
x_67 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_7, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_76 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_66, x_75, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_30 = lean_array_get_size(x_5);
x_31 = lean_expr_instantiate_rev_range(x_27, x_6, x_30, x_5);
lean_dec(x_30);
lean_dec(x_27);
x_32 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = (uint8_t)((x_29 << 24) >> 61);
lean_inc(x_33);
x_36 = lean_local_ctx_mk_local_decl(x_4, x_33, x_26, x_31, x_35);
x_37 = l_Lean_mkFVar(x_33);
x_38 = lean_array_push(x_5, x_37);
x_4 = x_36;
x_5 = x_38;
x_7 = x_28;
x_12 = x_34;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_array_get_size(x_5);
x_46 = lean_nat_dec_lt(x_45, x_44);
lean_dec(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_8, 1);
lean_dec(x_48);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_6);
lean_inc(x_5);
x_49 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(x_1, x_5, x_6, x_7, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_4);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(x_1, x_5, x_6, x_7, x_5, x_6, x_52, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_7);
x_54 = lean_expr_instantiate_rev_range(x_41, x_6, x_45, x_5);
lean_dec(x_45);
lean_dec(x_41);
x_55 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = (uint8_t)((x_43 << 24) >> 61);
lean_inc(x_56);
x_59 = lean_local_ctx_mk_local_decl(x_4, x_56, x_40, x_54, x_58);
x_60 = l_Lean_mkFVar(x_56);
x_61 = lean_array_push(x_5, x_60);
x_4 = x_59;
x_5 = x_61;
x_7 = x_42;
x_12 = x_57;
goto _start;
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_13 = x_63;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_5);
x_15 = lean_expr_instantiate_rev_range(x_7, x_6, x_14, x_5);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_4);
if (x_2 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(x_1, x_5, x_6, x_7, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_4);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_21);
if (x_2 == 0)
{
lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(x_1, x_5, x_6, x_7, x_5, x_6, x_22, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_5, x_6, x_22, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_17__forallTelescopeImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l_Array_empty___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg(x_2, x_12, x_11, x_9, x_13, x_14, x_1, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_17__forallTelescopeImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_17__forallTelescopeImpl___rarg), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__3___rarg(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Basic_17__forallTelescopeImpl___spec__1___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_17__forallTelescopeImpl___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_apply_2(x_3, x_5, x_6);
x_17 = lean_apply_7(x_4, lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_7, x_8);
x_19 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_8, x_26);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_27;
x_13 = x_25;
goto _start;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_33 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_18);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_32, x_41, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_58 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_22, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_8, x_61);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_62;
x_13 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_8, x_66);
lean_dec(x_8);
x_68 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_9, 2);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_18);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_67, x_76, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_58, 0);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_58);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
return x_19;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_19, 0);
x_102 = lean_ctor_get(x_19, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_19);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isForall(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_17 = lean_apply_2(x_1, x_2, x_3);
x_18 = lean_apply_7(x_4, lean_box(0), x_17, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg(x_5, lean_box(0), x_1, x_4, x_6, x_7, x_8, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_box(x_5);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1___boxed), 15, 9);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_8);
lean_closure_set(x_22, 2, x_12);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_1);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_11);
x_23 = lean_array_get_size(x_13);
x_24 = lean_nat_dec_lt(x_14, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(x_20, x_22, x_15, x_16, x_17, x_18, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_26 = lean_array_fget(x_13, x_14);
x_27 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_26, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_LocalDecl_type(x_28);
lean_dec(x_28);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_30);
x_31 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_30, x_15, x_16, x_17, x_18, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_26);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_14, x_34);
lean_dec(x_14);
x_2 = lean_box(0);
x_14 = x_35;
x_19 = x_33;
goto _start;
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_14, x_39);
lean_dec(x_14);
x_41 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_16, x_17, x_18, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 2);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_26);
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_50 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_40, x_49, x_16, x_17, x_18, x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_restoreSynthInstanceCache(x_42, x_15, x_16, x_17, x_18, x_52);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
x_60 = l_Lean_Meta_restoreSynthInstanceCache(x_42, x_15, x_16, x_17, x_18, x_59);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
lean_dec(x_31);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_66 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_30, x_15, x_16, x_17, x_18, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_26);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_14, x_69);
lean_dec(x_14);
x_2 = lean_box(0);
x_14 = x_70;
x_19 = x_68;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_14, x_74);
lean_dec(x_14);
x_76 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_16, x_17, x_18, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_15, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_15, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_15, 2);
lean_inc(x_81);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_26);
x_83 = lean_array_push(x_81, x_82);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_85 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_75, x_84, x_16, x_17, x_18, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_restoreSynthInstanceCache(x_77, x_15, x_16, x_17, x_18, x_87);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_dec(x_85);
x_95 = l_Lean_Meta_restoreSynthInstanceCache(x_77, x_15, x_16, x_17, x_18, x_94);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_66);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_66, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_66);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_31);
if (x_104 == 0)
{
return x_31;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_31, 0);
x_106 = lean_ctor_get(x_31, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_31);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_27);
if (x_108 == 0)
{
return x_27;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_27, 0);
x_110 = lean_ctor_get(x_27, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_27);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___boxed), 19, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_apply_2(x_3, x_5, x_6);
x_17 = lean_apply_7(x_4, lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_7, x_8);
x_19 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_8, x_26);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_27;
x_13 = x_25;
goto _start;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_33 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_18);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_32, x_41, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_58 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_22, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_8, x_61);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_62;
x_13 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_8, x_66);
lean_dec(x_8);
x_68 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_9, 2);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_18);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_67, x_76, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_58, 0);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_58);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
return x_19;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_19, 0);
x_102 = lean_ctor_get(x_19, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_19);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
if (lean_obj_tag(x_10) == 7)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_33 = lean_array_get_size(x_8);
x_34 = lean_expr_instantiate_rev_range(x_30, x_9, x_33, x_8);
lean_dec(x_33);
lean_dec(x_30);
x_35 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_14, x_15);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = (uint8_t)((x_32 << 24) >> 61);
lean_inc(x_36);
x_39 = lean_local_ctx_mk_local_decl(x_7, x_36, x_29, x_34, x_38);
x_40 = l_Lean_mkFVar(x_36);
x_41 = lean_array_push(x_8, x_40);
x_2 = lean_box(0);
x_7 = x_39;
x_8 = x_41;
x_10 = x_31;
x_15 = x_37;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_8);
x_49 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_6);
x_50 = lean_expr_instantiate_rev_range(x_10, x_9, x_48, x_8);
lean_dec(x_48);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_11, 1);
lean_dec(x_52);
lean_ctor_set(x_11, 1, x_7);
lean_inc(x_8);
x_53 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_50, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_7);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_8);
x_57 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_50, x_8, x_9, x_56, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
x_58 = lean_expr_instantiate_rev_range(x_44, x_9, x_48, x_8);
lean_dec(x_48);
lean_dec(x_44);
x_59 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_14, x_15);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = (uint8_t)((x_46 << 24) >> 61);
lean_inc(x_60);
x_63 = lean_local_ctx_mk_local_decl(x_7, x_60, x_43, x_58, x_62);
x_64 = l_Lean_mkFVar(x_60);
x_65 = lean_array_push(x_8, x_64);
x_2 = lean_box(0);
x_7 = x_63;
x_8 = x_65;
x_10 = x_45;
x_15 = x_61;
goto _start;
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_16 = x_67;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_17 = lean_array_get_size(x_8);
x_18 = lean_expr_instantiate_rev_range(x_10, x_9, x_17, x_8);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_11, 1);
lean_dec(x_20);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_7);
if (x_5 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_8);
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_18, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_8);
x_22 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_7);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_24);
if (x_5 == 0)
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_8);
x_26 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_18, x_8, x_9, x_25, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_8);
x_27 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_8, x_9, x_25, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg___boxed), 15, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_12 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_isForall(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_16 = l_Array_empty___closed__1;
x_17 = lean_apply_2(x_3, x_16, x_5);
x_18 = lean_apply_7(x_4, lean_box(0), x_17, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_19 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_7, x_8, x_9, x_10, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = l_Array_empty___closed__1;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg(x_1, lean_box(0), x_3, x_4, x_22, x_6, x_20, x_23, x_24, x_13, x_7, x_8, x_9, x_10, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallTelescopeReducing___spec__1___rarg(x_1, lean_box(0), x_2, x_4, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1), 9, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_4);
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
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__4___rarg(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallTelescopeReducing___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescopeReducing___spec__2___rarg(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_apply_2(x_3, x_5, x_6);
x_17 = lean_apply_7(x_4, lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_7, x_8);
x_19 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_8, x_26);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_27;
x_13 = x_25;
goto _start;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_33 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_18);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_32, x_41, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_58 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_22, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_8, x_61);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_62;
x_13 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_8, x_66);
lean_dec(x_8);
x_68 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_9, 2);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_18);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_67, x_76, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_58, 0);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_58);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
return x_19;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_19, 0);
x_102 = lean_ctor_get(x_19, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_19);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isForall(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_17 = lean_apply_2(x_1, x_2, x_3);
x_18 = lean_apply_7(x_4, lean_box(0), x_17, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg(x_5, lean_box(0), x_1, x_4, x_6, x_7, x_8, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_box(x_5);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1___boxed), 15, 9);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_8);
lean_closure_set(x_22, 2, x_12);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_1);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_11);
x_23 = lean_array_get_size(x_13);
x_24 = lean_nat_dec_lt(x_14, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(x_20, x_22, x_15, x_16, x_17, x_18, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_26 = lean_array_fget(x_13, x_14);
x_27 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_26, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_LocalDecl_type(x_28);
lean_dec(x_28);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_30);
x_31 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_30, x_15, x_16, x_17, x_18, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_26);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_14, x_34);
lean_dec(x_14);
x_2 = lean_box(0);
x_14 = x_35;
x_19 = x_33;
goto _start;
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_14, x_39);
lean_dec(x_14);
x_41 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_16, x_17, x_18, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 2);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_26);
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_50 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_40, x_49, x_16, x_17, x_18, x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_restoreSynthInstanceCache(x_42, x_15, x_16, x_17, x_18, x_52);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
x_60 = l_Lean_Meta_restoreSynthInstanceCache(x_42, x_15, x_16, x_17, x_18, x_59);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
lean_dec(x_31);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_66 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_30, x_15, x_16, x_17, x_18, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_26);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_14, x_69);
lean_dec(x_14);
x_2 = lean_box(0);
x_14 = x_70;
x_19 = x_68;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_14, x_74);
lean_dec(x_14);
x_76 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_16, x_17, x_18, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_15, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_15, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_15, 2);
lean_inc(x_81);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_26);
x_83 = lean_array_push(x_81, x_82);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_85 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_75, x_84, x_16, x_17, x_18, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_restoreSynthInstanceCache(x_77, x_15, x_16, x_17, x_18, x_87);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_dec(x_85);
x_95 = l_Lean_Meta_restoreSynthInstanceCache(x_77, x_15, x_16, x_17, x_18, x_94);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_66);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_66, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_66);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_31);
if (x_104 == 0)
{
return x_31;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_31, 0);
x_106 = lean_ctor_get(x_31, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_31);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_27);
if (x_108 == 0)
{
return x_27;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_27, 0);
x_110 = lean_ctor_get(x_27, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_27);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___boxed), 19, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_apply_2(x_3, x_5, x_6);
x_17 = lean_apply_7(x_4, lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_7, x_8);
x_19 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_8, x_26);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_27;
x_13 = x_25;
goto _start;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_33 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_18);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_32, x_41, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Lean_Meta_restoreSynthInstanceCache(x_34, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_58 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_22, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_8, x_61);
lean_dec(x_8);
x_2 = lean_box(0);
x_8 = x_62;
x_13 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_8, x_66);
lean_dec(x_8);
x_68 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_10, x_11, x_12, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_9, 2);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_18);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_67, x_76, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Meta_restoreSynthInstanceCache(x_69, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_58);
if (x_92 == 0)
{
return x_58;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_58, 0);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_58);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
return x_19;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_19, 0);
x_102 = lean_ctor_get(x_19, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_19);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
if (lean_obj_tag(x_10) == 7)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_33 = lean_array_get_size(x_8);
x_34 = lean_expr_instantiate_rev_range(x_30, x_9, x_33, x_8);
lean_dec(x_33);
lean_dec(x_30);
x_35 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_14, x_15);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = (uint8_t)((x_32 << 24) >> 61);
lean_inc(x_36);
x_39 = lean_local_ctx_mk_local_decl(x_7, x_36, x_29, x_34, x_38);
x_40 = l_Lean_mkFVar(x_36);
x_41 = lean_array_push(x_8, x_40);
x_2 = lean_box(0);
x_7 = x_39;
x_8 = x_41;
x_10 = x_31;
x_15 = x_37;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_8);
x_49 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_6);
x_50 = lean_expr_instantiate_rev_range(x_10, x_9, x_48, x_8);
lean_dec(x_48);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_11, 1);
lean_dec(x_52);
lean_ctor_set(x_11, 1, x_7);
lean_inc(x_8);
x_53 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_50, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_7);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_8);
x_57 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_50, x_8, x_9, x_56, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
x_58 = lean_expr_instantiate_rev_range(x_44, x_9, x_48, x_8);
lean_dec(x_48);
lean_dec(x_44);
x_59 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_14, x_15);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = (uint8_t)((x_46 << 24) >> 61);
lean_inc(x_60);
x_63 = lean_local_ctx_mk_local_decl(x_7, x_60, x_43, x_58, x_62);
x_64 = l_Lean_mkFVar(x_60);
x_65 = lean_array_push(x_8, x_64);
x_2 = lean_box(0);
x_7 = x_63;
x_8 = x_65;
x_10 = x_45;
x_15 = x_61;
goto _start;
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_16 = x_67;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_17 = lean_array_get_size(x_8);
x_18 = lean_expr_instantiate_rev_range(x_10, x_9, x_17, x_8);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_11, 1);
lean_dec(x_20);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_7);
if (x_5 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_8);
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_18, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_8);
x_22 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_7);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_24);
if (x_5 == 0)
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_8);
x_26 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_8, x_18, x_8, x_9, x_25, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_8);
x_27 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_8, x_9, x_25, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg___boxed), 15, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_12 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_isForall(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_16 = l_Array_empty___closed__1;
x_17 = lean_apply_2(x_3, x_16, x_5);
x_18 = lean_apply_7(x_4, lean_box(0), x_17, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_19 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_7, x_8, x_9, x_10, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = l_Array_empty___closed__1;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg(x_1, lean_box(0), x_3, x_4, x_22, x_6, x_20, x_23, x_24, x_13, x_7, x_8, x_9, x_10, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_forallBoundedTelescope___spec__1___rarg(x_1, lean_box(0), x_2, x_5, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1), 10, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
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
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__4___rarg(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_forallBoundedTelescope___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallBoundedTelescope___spec__2___rarg(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_expr_instantiate_rev_range(x_4, x_3, x_12, x_2);
lean_dec(x_12);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_apply_7(x_1, x_2, x_13, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_17 = lean_array_fget(x_5, x_6);
x_18 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_6 = x_26;
x_11 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_41 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_31, x_40, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_21, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_6, x_60);
lean_dec(x_6);
x_6 = x_61;
x_11 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_6, x_65);
lean_dec(x_6);
x_67 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_8, x_9, x_10, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_7, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_76 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_66, x_75, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
switch (lean_obj_tag(x_5)) {
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_24 = lean_array_get_size(x_3);
x_25 = lean_expr_instantiate_rev_range(x_21, x_4, x_24, x_3);
lean_dec(x_24);
lean_dec(x_21);
x_26 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_9, x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = (uint8_t)((x_23 << 24) >> 61);
lean_inc(x_27);
x_30 = lean_local_ctx_mk_local_decl(x_2, x_27, x_20, x_25, x_29);
x_31 = l_Lean_mkFVar(x_27);
x_32 = lean_array_push(x_3, x_31);
x_2 = x_30;
x_3 = x_32;
x_5 = x_22;
x_10 = x_28;
goto _start;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 3);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_array_get_size(x_3);
x_39 = lean_expr_instantiate_rev_range(x_35, x_4, x_38, x_3);
lean_dec(x_35);
x_40 = lean_expr_instantiate_rev_range(x_36, x_4, x_38, x_3);
lean_dec(x_38);
lean_dec(x_36);
x_41 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_9, x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_42);
x_44 = lean_local_ctx_mk_let_decl(x_2, x_42, x_34, x_39, x_40);
x_45 = l_Lean_mkFVar(x_42);
x_46 = lean_array_push(x_3, x_45);
x_2 = x_44;
x_3 = x_46;
x_5 = x_37;
x_10 = x_43;
goto _start;
}
default: 
{
lean_object* x_48; 
x_48 = lean_box(0);
x_11 = x_48;
goto block_19;
}
}
block_19:
{
uint8_t x_12; 
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
lean_ctor_set(x_6, 1, x_2);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(x_1, x_3, x_4, x_5, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(x_1, x_3, x_4, x_5, x_3, x_4, x_17, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Basic_18__lambdaTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_empty___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Meta_Basic_18__lambdaTelescopeAux___main___rarg(x_2, x_9, x_11, x_12, x_1, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_19__lambdaTelescopeImpl___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_7);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_17, x_2, x_3, x_4, x_5, x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = lean_environment_find(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = x_2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_2, x_1, x_13);
x_15 = x_12;
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
x_17 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_20;
x_24 = lean_array_fset(x_14, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_1);
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
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_12 = x_2;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = x_14;
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_3, x_4);
x_18 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_4 = x_26;
x_9 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_32 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(x_1, x_2, x_3, x_31, x_40, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_21, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
lean_dec(x_4);
x_4 = x_61;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
lean_dec(x_4);
x_67 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(x_1, x_2, x_3, x_66, x_75, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = x_1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = x_16;
x_18 = lean_apply_5(x_17, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4(x_2, x_3, x_4, x_5, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_expr_instantiate_rev_range(x_7, x_6, x_8, x_5);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_box(x_2);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1___boxed), 12, 6);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_8);
x_20 = lean_array_get_size(x_9);
x_21 = lean_nat_dec_lt(x_10, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(x_17, x_19, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
x_23 = lean_array_fget(x_9, x_10);
x_24 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_23, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_type(x_25);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_27, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_23);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
x_10 = x_32;
x_15 = x_30;
goto _start;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_10, x_36);
lean_dec(x_10);
x_38 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_23);
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_47 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37, x_46, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_11, x_12, x_13, x_14, x_49);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_11, x_12, x_13, x_14, x_56);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_27, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_10, x_66);
lean_dec(x_10);
x_10 = x_67;
x_15 = x_65;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_10, x_71);
lean_dec(x_10);
x_73 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_23);
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_80);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_82 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72, x_81, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_11, x_12, x_13, x_14, x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set_tag(x_92, 1);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_63);
if (x_97 == 0)
{
return x_63;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_63, 0);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_63);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_28);
if (x_101 == 0)
{
return x_28;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_28, 0);
x_103 = lean_ctor_get(x_28, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_28);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_24);
if (x_105 == 0)
{
return x_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_24, 0);
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_24);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_12 = x_2;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = x_14;
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_3, x_4);
x_18 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_4 = x_26;
x_9 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_32 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(x_1, x_2, x_3, x_31, x_40, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_21, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
lean_dec(x_4);
x_4 = x_61;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
lean_dec(x_4);
x_67 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(x_1, x_2, x_3, x_66, x_75, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_29 = lean_array_get_size(x_5);
x_30 = lean_expr_instantiate_rev_range(x_26, x_6, x_29, x_5);
lean_dec(x_29);
lean_dec(x_26);
x_31 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = (uint8_t)((x_28 << 24) >> 61);
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_4, x_32, x_25, x_30, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_5, x_36);
x_4 = x_35;
x_5 = x_37;
x_7 = x_27;
x_12 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_5);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_8, 1);
lean_dec(x_47);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_5);
x_48 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(x_1, x_5, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_5);
x_52 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(x_1, x_5, x_5, x_6, x_51, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_expr_instantiate_rev_range(x_40, x_6, x_44, x_5);
lean_dec(x_44);
lean_dec(x_40);
x_54 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = (uint8_t)((x_42 << 24) >> 61);
lean_inc(x_55);
x_58 = lean_local_ctx_mk_local_decl(x_4, x_55, x_39, x_53, x_57);
x_59 = l_Lean_mkFVar(x_55);
x_60 = lean_array_push(x_5, x_59);
x_4 = x_58;
x_5 = x_60;
x_7 = x_41;
x_12 = x_56;
goto _start;
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_13 = x_62;
goto block_24;
}
block_24:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_5);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_4);
if (x_2 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_5);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(x_1, x_5, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
if (x_2 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_5);
x_22 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(x_1, x_5, x_5, x_6, x_21, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_5, x_6, x_21, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1;
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2;
x_14 = x_13;
x_15 = lean_apply_5(x_14, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_4, x_5, x_6, x_7, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = l_Array_empty___closed__1;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4(x_1, x_19, x_3, x_17, x_20, x_21, x_10, x_4, x_5, x_6, x_7, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* _init_l_Lean_Meta_getParamNamesImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_monadControlRefl___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_getParamNamesImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_getParamNamesImpl___closed__1;
x_13 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3(x_12, x_10, x_11, x_2, x_3, x_4, x_5, x_9);
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
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_umapMAux___main___at_Lean_Meta_getParamNamesImpl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__6(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_Meta_getParamNamesImpl___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_Meta_getParamNamesImpl___spec__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Meta_getParamNames___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNamesImpl), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_getParamNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_43 = lean_array_get_size(x_4);
x_44 = lean_expr_instantiate_rev_range(x_40, x_6, x_43, x_4);
lean_dec(x_43);
lean_dec(x_40);
x_45 = (uint8_t)((x_42 << 24) >> 61);
x_46 = l_Lean_BinderInfo_isInstImplicit(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_47, x_3, x_39, x_8, x_9, x_10, x_11, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_push(x_4, x_49);
x_52 = lean_box(x_45);
x_53 = lean_array_push(x_5, x_52);
x_4 = x_51;
x_5 = x_53;
x_7 = x_41;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = 1;
x_56 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_47, x_55, x_39, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_push(x_4, x_57);
x_60 = lean_box(x_45);
x_61 = lean_array_push(x_5, x_60);
x_4 = x_59;
x_5 = x_61;
x_7 = x_41;
x_12 = x_58;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_7, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_7, 2);
lean_inc(x_65);
x_66 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_array_get_size(x_4);
x_69 = lean_nat_dec_lt(x_68, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_70 = lean_expr_instantiate_rev_range(x_7, x_6, x_68, x_4);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_7);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; 
lean_dec(x_7);
x_74 = lean_expr_instantiate_rev_range(x_64, x_6, x_68, x_4);
lean_dec(x_68);
lean_dec(x_64);
x_75 = (uint8_t)((x_66 << 24) >> 61);
x_76 = l_Lean_BinderInfo_isInstImplicit(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_74);
if (x_76 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_77, x_3, x_63, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_array_push(x_4, x_79);
x_82 = lean_box(x_75);
x_83 = lean_array_push(x_5, x_82);
x_4 = x_81;
x_5 = x_83;
x_7 = x_65;
x_12 = x_80;
goto _start;
}
else
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = 1;
x_86 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_77, x_85, x_63, x_8, x_9, x_10, x_11, x_12);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_array_push(x_4, x_87);
x_90 = lean_box(x_75);
x_91 = lean_array_push(x_5, x_90);
x_4 = x_89;
x_5 = x_91;
x_7 = x_65;
x_12 = x_88;
goto _start;
}
}
}
}
else
{
lean_object* x_93; 
x_93 = lean_box(0);
x_13 = x_93;
goto block_38;
}
block_38:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_4);
x_15 = lean_expr_instantiate_rev_range(x_7, x_6, x_14, x_4);
lean_dec(x_6);
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_15);
x_19 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_isForall(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_free_object(x_19);
lean_dec(x_15);
x_6 = x_14;
x_7 = x_21;
x_12 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = l_Lean_Expr_isForall(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_15);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_dec(x_15);
x_6 = x_14;
x_7 = x_27;
x_12 = x_28;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main(x_13, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux(x_13, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Lean_Meta_forallMetaTelescope___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = l_Array_empty___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(x_5);
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___boxed), 12, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_6);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_7);
lean_closure_set(x_10, 6, x_2);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallMetaTelescope___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallMetaTelescope___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Meta_forallMetaTelescope___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = 1;
x_6 = l_Array_empty___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(x_5);
x_9 = lean_box(x_4);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_20__forallMetaTelescopeReducingAux___boxed), 12, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_6);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_7);
lean_closure_set(x_10, 6, x_2);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallMetaTelescopeReducing___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Meta_forallMetaTelescopeReducing___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10);
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
x_46 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_43, x_44, x_45, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Array_empty___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_21__lambdaMetaTelescopeAux___boxed), 10, 5);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
lean_closure_set(x_6, 4, x_2);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaMetaTelescope___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_22__withNewFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_22__withNewFVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_2, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_13);
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
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = lean_apply_6(x_3, x_1, x_23, x_5, x_6, x_7, x_17);
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
lean_object* l___private_Lean_Meta_Basic_22__withNewFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_22__withNewFVar___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_3);
lean_inc(x_11);
x_17 = lean_local_ctx_mk_local_decl(x_15, x_11, x_1, x_3, x_2);
x_18 = l_Lean_mkFVar(x_11);
lean_inc(x_16);
lean_inc(x_17);
lean_inc(x_14);
lean_ctor_set(x_5, 1, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_3, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_4, x_18, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_18);
x_29 = lean_array_push(x_16, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = lean_apply_6(x_4, x_18, x_30, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_restoreSynthInstanceCache(x_26, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lean_Meta_restoreSynthInstanceCache(x_26, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
x_52 = lean_ctor_get(x_5, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_11);
x_53 = lean_local_ctx_mk_local_decl(x_51, x_11, x_1, x_3, x_2);
x_54 = l_Lean_mkFVar(x_11);
lean_inc(x_52);
lean_inc(x_53);
lean_inc(x_50);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_55);
x_56 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_3, x_55, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_apply_6(x_4, x_54, x_55, x_6, x_7, x_8, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_54);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_54);
x_66 = lean_array_push(x_52, x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_53);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = lean_apply_6(x_4, x_54, x_67, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_restoreSynthInstanceCache(x_63, x_55, x_6, x_7, x_8, x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_55);
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
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_dec(x_68);
x_77 = l_Lean_Meta_restoreSynthInstanceCache(x_63, x_55, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_55);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_81 = lean_ctor_get(x_56, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_56, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_83 = x_56;
} else {
 lean_dec_ref(x_56);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_12 = l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_withLocalDeclD___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg___lambda__1), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(x_2, x_11, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___rarg___lambda__1), 9, 3);
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
lean_object* l_Lean_Meta_withLocalDeclD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_24__withLetDeclImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_2);
lean_inc(x_11);
x_17 = lean_local_ctx_mk_let_decl(x_15, x_11, x_1, x_2, x_3);
x_18 = l_Lean_mkFVar(x_11);
lean_inc(x_16);
lean_inc(x_17);
lean_inc(x_14);
lean_ctor_set(x_5, 1, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_2, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_4, x_18, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_18);
x_29 = lean_array_push(x_16, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = lean_apply_6(x_4, x_18, x_30, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_restoreSynthInstanceCache(x_26, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lean_Meta_restoreSynthInstanceCache(x_26, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
x_52 = lean_ctor_get(x_5, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_11);
x_53 = lean_local_ctx_mk_let_decl(x_51, x_11, x_1, x_2, x_3);
x_54 = l_Lean_mkFVar(x_11);
lean_inc(x_52);
lean_inc(x_53);
lean_inc(x_50);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_55);
x_56 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_2, x_55, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_apply_6(x_4, x_54, x_55, x_6, x_7, x_8, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_54);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_54);
x_66 = lean_array_push(x_52, x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_53);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = lean_apply_6(x_4, x_54, x_67, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_restoreSynthInstanceCache(x_63, x_55, x_6, x_7, x_8, x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_55);
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
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_dec(x_68);
x_77 = l_Lean_Meta_restoreSynthInstanceCache(x_63, x_55, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_55);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_81 = lean_ctor_get(x_56, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_56, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_83 = x_56;
} else {
 lean_dec_ref(x_56);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_24__withLetDeclImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_24__withLetDeclImpl___rarg), 9, 0);
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
x_12 = l___private_Lean_Meta_Basic_24__withLetDeclImpl___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_List_foldl___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l___private_Lean_Meta_Basic_16__isClassImpl_x3f(x_11, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_List_foldl___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__1(x_10, x_1);
lean_inc(x_11);
lean_inc(x_13);
lean_inc(x_9);
lean_ctor_set(x_3, 1, x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2(x_11, x_1, x_3, x_4, x_5, x_6, x_7);
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
x_47 = l_List_foldl___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__1(x_44, x_1);
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
x_49 = l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2(x_45, x_1, x_48, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_25__withExistingLocalDeclsImpl___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Meta_Basic_26__withNewMCtxDepthImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_MetavarContext_incDepth(x_15);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
x_36 = lean_ctor_get(x_12, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_37 = l_Lean_MetavarContext_incDepth(x_34);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
x_39 = lean_st_ref_set(x_3, x_38, x_13);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_2, x_3, x_4, x_5, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_26__withNewMCtxDepthImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_26__withNewMCtxDepthImpl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_4, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_MetavarContext_incDepth(x_16);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_4, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_11, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_11, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
x_37 = lean_ctor_get(x_13, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_38 = l_Lean_MetavarContext_incDepth(x_35);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_st_ref_set(x_4, x_39, x_14);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_11, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_11, x_3, x_4, x_5, x_6, x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
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
uint8_t l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_4, x_5, x_6, x_7, x_8);
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
x_37 = l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1(x_2, x_10, lean_box(0), x_2, x_10, x_36);
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
x_76 = l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1(x_2, x_10, lean_box(0), x_2, x_10, x_75);
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
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at___private_Lean_Meta_Basic_27__withLocalContextImpl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_11 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Meta_Basic_28__withMVarContextImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_10);
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
lean_object* l___private_Lean_Meta_Basic_28__withMVarContextImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_28__withMVarContextImpl___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 4);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_13, x_14, x_9, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
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
lean_object* l___private_Lean_Meta_Basic_29__withMCtxImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_1, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_9, x_3, x_4, x_5, x_6, x_15);
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
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_9, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_29__withMCtxImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_29__withMCtxImpl___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_1, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_10, x_4, x_5, x_6, x_7, x_23);
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
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
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
lean_object* l_Lean_Meta_withMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_30__approxDefEqImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get_uint8(x_8, 3);
x_21 = lean_ctor_get_uint8(x_8, 4);
x_22 = lean_ctor_get_uint8(x_8, 5);
lean_dec(x_8);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, 3, x_20);
lean_ctor_set_uint8(x_24, 4, x_21);
lean_ctor_set_uint8(x_24, 5, x_22);
lean_ctor_set(x_2, 0, x_24);
x_25 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_37 = lean_ctor_get_uint8(x_34, 3);
x_38 = lean_ctor_get_uint8(x_34, 4);
x_39 = lean_ctor_get_uint8(x_34, 5);
if (lean_is_exclusive(x_34)) {
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
x_41 = 1;
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 0, 6);
} else {
 x_42 = x_40;
}
lean_ctor_set_uint8(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, 2, x_41);
lean_ctor_set_uint8(x_42, 3, x_37);
lean_ctor_set_uint8(x_42, 4, x_38);
lean_ctor_set_uint8(x_42, 5, x_39);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
x_44 = lean_apply_5(x_1, x_43, x_3, x_4, x_5, x_6);
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
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_30__approxDefEqImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_30__approxDefEqImpl___rarg), 6, 0);
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
lean_dec(x_9);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, 2, x_24);
lean_ctor_set_uint8(x_25, 3, x_21);
lean_ctor_set_uint8(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, 5, x_23);
lean_ctor_set(x_3, 0, x_25);
x_26 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_38 = lean_ctor_get_uint8(x_35, 3);
x_39 = lean_ctor_get_uint8(x_35, 4);
x_40 = lean_ctor_get_uint8(x_35, 5);
if (lean_is_exclusive(x_35)) {
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = 1;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 0, 6);
} else {
 x_43 = x_41;
}
lean_ctor_set_uint8(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, 3, x_38);
lean_ctor_set_uint8(x_43, 4, x_39);
lean_ctor_set_uint8(x_43, 5, x_40);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
x_45 = lean_apply_7(x_2, lean_box(0), x_1, x_44, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
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
lean_object* l___private_Lean_Meta_Basic_31__fullApproxDefEqImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get_uint8(x_8, 4);
x_21 = lean_ctor_get_uint8(x_8, 5);
lean_dec(x_8);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, 3, x_22);
lean_ctor_set_uint8(x_23, 4, x_20);
lean_ctor_set_uint8(x_23, 5, x_21);
lean_ctor_set(x_2, 0, x_23);
x_24 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_36 = lean_ctor_get_uint8(x_33, 4);
x_37 = lean_ctor_get_uint8(x_33, 5);
if (lean_is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean_dec_ref(x_33);
 x_38 = lean_box(0);
}
x_39 = 1;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 0, 6);
} else {
 x_40 = x_38;
}
lean_ctor_set_uint8(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, 2, x_39);
lean_ctor_set_uint8(x_40, 3, x_39);
lean_ctor_set_uint8(x_40, 4, x_36);
lean_ctor_set_uint8(x_40, 5, x_37);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_35);
x_42 = lean_apply_5(x_1, x_41, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
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
lean_object* l___private_Lean_Meta_Basic_31__fullApproxDefEqImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_31__fullApproxDefEqImpl___rarg), 6, 0);
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get_uint8(x_9, 4);
x_22 = lean_ctor_get_uint8(x_9, 5);
lean_dec(x_9);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, 4, x_21);
lean_ctor_set_uint8(x_24, 5, x_22);
lean_ctor_set(x_3, 0, x_24);
x_25 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_37 = lean_ctor_get_uint8(x_34, 4);
x_38 = lean_ctor_get_uint8(x_34, 5);
if (lean_is_exclusive(x_34)) {
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
x_40 = 1;
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 0, 6);
} else {
 x_41 = x_39;
}
lean_ctor_set_uint8(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, 2, x_40);
lean_ctor_set_uint8(x_41, 3, x_40);
lean_ctor_set_uint8(x_41, 4, x_37);
lean_ctor_set_uint8(x_41, 5, x_38);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
x_43 = lean_apply_7(x_2, lean_box(0), x_1, x_42, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
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
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_12, x_2, x_3, x_4, x_5, x_9);
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
}
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateLevelMVars), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_32__liftStateMCtx___rarg___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLevelMVars___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_12, x_2, x_3, x_4, x_5, x_9);
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
}
lean_object* l_Lean_Meta_normalizeLevel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Level_normalize___main(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_normalizeLevel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_normalizeLevel___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_normalizeLevel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_normalizeLevel___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_normalizeLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_normalizeLevel___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_normalizeLevel___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normalizeLevel___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_assignLevelMVar___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_metavar_ctx_assign_level(x_11, x_1, x_2);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = lean_metavar_ctx_assign_level(x_20, x_1, x_2);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
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
lean_object* l_Lean_Meta_assignLevelMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_assignLevelMVar___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_assignLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_assignLevelMVar___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_assignLevelMVar___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_assignLevelMVar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_whnfD___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_27, 0, x_21);
lean_ctor_set_uint8(x_27, 1, x_22);
lean_ctor_set_uint8(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, 3, x_24);
lean_ctor_set_uint8(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, 5, x_26);
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
x_40 = lean_ctor_get_uint8(x_37, 0);
x_41 = lean_ctor_get_uint8(x_37, 1);
x_42 = lean_ctor_get_uint8(x_37, 2);
x_43 = lean_ctor_get_uint8(x_37, 3);
x_44 = lean_ctor_get_uint8(x_37, 4);
if (lean_is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 6);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_40);
lean_ctor_set_uint8(x_47, 1, x_41);
lean_ctor_set_uint8(x_47, 2, x_42);
lean_ctor_set_uint8(x_47, 3, x_43);
lean_ctor_set_uint8(x_47, 4, x_44);
lean_ctor_set_uint8(x_47, 5, x_46);
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
lean_object* l_Lean_Meta_whnfD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Meta_whnf___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_whnfD___rarg___lambda__1), 7, 1);
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
lean_object* l_Lean_Meta_whnfD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfD___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_5, x_21, x_9);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_add_decl(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_15;
}
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_compile_decl(x_10, x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(x_15, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_16;
}
}
}
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Closure_mkValueTypeClosure(x_11, x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_19, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; uint32_t x_33; uint32_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_st_ref_get(x_8, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = l_Array_toList___rarg(x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_28);
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_ctor_get(x_21, 2);
lean_inc(x_30);
lean_inc(x_30);
lean_inc(x_25);
x_31 = l_Lean_getMaxHeight(x_25, x_30);
x_32 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_33 = 1;
x_34 = x_32 + x_33;
x_35 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_35, 0, x_34);
lean_inc(x_25);
x_36 = l_Lean_Environment_hasUnsafe(x_25, x_28);
x_37 = lean_ctor_get(x_21, 5);
lean_inc(x_37);
x_38 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_37, x_5, x_6, x_7, x_8, x_24);
if (x_36 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_30);
x_40 = l_Lean_Environment_hasUnsafe(x_25, x_30);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1(x_42, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_21, 3);
lean_inc(x_46);
x_47 = l_Array_toList___rarg(x_46);
lean_dec(x_46);
x_48 = l_Lean_mkConst(x_1, x_47);
x_49 = lean_ctor_get(x_21, 4);
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_49, x_49, x_50, x_48);
lean_dec(x_49);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_21, 3);
lean_inc(x_53);
x_54 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_55 = l_Lean_mkConst(x_1, x_54);
x_56 = lean_ctor_get(x_21, 4);
lean_inc(x_56);
lean_dec(x_21);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_56, x_56, x_57, x_55);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
return x_43;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_43);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_25);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_29);
lean_ctor_set(x_66, 1, x_30);
lean_ctor_set(x_66, 2, x_35);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1(x_67, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_21, 3);
lean_inc(x_71);
x_72 = l_Array_toList___rarg(x_71);
lean_dec(x_71);
x_73 = l_Lean_mkConst(x_1, x_72);
x_74 = lean_ctor_get(x_21, 4);
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_74, x_74, x_75, x_73);
lean_dec(x_74);
lean_ctor_set(x_68, 0, x_76);
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = lean_ctor_get(x_21, 3);
lean_inc(x_78);
x_79 = l_Array_toList___rarg(x_78);
lean_dec(x_78);
x_80 = l_Lean_mkConst(x_1, x_79);
x_81 = lean_ctor_get(x_21, 4);
lean_inc(x_81);
lean_dec(x_21);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_81, x_81, x_82, x_80);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_21);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_68);
if (x_85 == 0)
{
return x_68;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_68, 0);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_68);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addAndCompile___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___boxed), 9, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Meta_mkAuxDefinition___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_inferTypeRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_inferTypeRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_headBeta(x_3);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_33__mkAuxDefinitionImp(x_1, x_9, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Compiler_inlineAttrs;
x_10 = lean_box(x_2);
x_11 = l_Lean_EnumAttributes_setValue___rarg(x_9, x_3, x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_setEnv___at___private_Lean_Meta_Basic_33__mkAuxDefinitionImp___spec__4(x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
lean_object* _init_l_Lean_Meta_setInlineAttribute___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_setInlineAttribute___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_setInlineAttribute___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_setInlineAttribute___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_setInlineAttribute___rarg___lambda__2___boxed), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Meta_setInlineAttribute___rarg___closed__2;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_setInlineAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_setInlineAttribute___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_setInlineAttribute___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_setInlineAttribute___rarg___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_setInlineAttribute___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Meta_setInlineAttribute___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid instantiateForall, too many parameters");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3;
x_23 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_22, x_4, x_5, x_6, x_7, x_21);
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
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_34__instantiateForallAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_34__instantiateForallAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Basic_34__instantiateForallAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_34__instantiateForallAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateForall___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_34__instantiateForallAux___boxed), 8, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_instantiateForall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___rarg), 3, 0);
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
lean_object* initialize_Lean_Util_Closure(lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(lean_object*);
lean_object* initialize_Lean_Meta_Exception(lean_object*);
lean_object* initialize_Lean_Meta_TransparencyMode(lean_object*);
lean_object* initialize_Lean_Meta_DiscrTreeTypes(lean_object*);
lean_object* initialize_Lean_Eval(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
res = initialize_Lean_Util_Closure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Exception(lean_io_mk_world());
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
l_Lean_Meta_ParamInfo_inhabited___closed__1 = _init_l_Lean_Meta_ParamInfo_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_ParamInfo_inhabited___closed__1);
l_Lean_Meta_ParamInfo_inhabited = _init_l_Lean_Meta_ParamInfo_inhabited();
lean_mark_persistent(l_Lean_Meta_ParamInfo_inhabited);
l_Lean_Meta_InfoCacheKey_Inhabited___closed__1 = _init_l_Lean_Meta_InfoCacheKey_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InfoCacheKey_Inhabited___closed__1);
l_Lean_Meta_InfoCacheKey_Inhabited = _init_l_Lean_Meta_InfoCacheKey_Inhabited();
lean_mark_persistent(l_Lean_Meta_InfoCacheKey_Inhabited);
l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1___closed__1);
l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__1);
l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2___closed__1);
l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_State_inhabited___spec__2);
l_Lean_Meta_State_inhabited___closed__1 = _init_l_Lean_Meta_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_State_inhabited___closed__1);
l_Lean_Meta_State_inhabited___closed__2 = _init_l_Lean_Meta_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Meta_State_inhabited___closed__2);
l_Lean_Meta_State_inhabited___closed__3 = _init_l_Lean_Meta_State_inhabited___closed__3();
lean_mark_persistent(l_Lean_Meta_State_inhabited___closed__3);
l_Lean_Meta_State_inhabited___closed__4 = _init_l_Lean_Meta_State_inhabited___closed__4();
lean_mark_persistent(l_Lean_Meta_State_inhabited___closed__4);
l_Lean_Meta_State_inhabited___closed__5 = _init_l_Lean_Meta_State_inhabited___closed__5();
lean_mark_persistent(l_Lean_Meta_State_inhabited___closed__5);
l_Lean_Meta_State_inhabited = _init_l_Lean_Meta_State_inhabited();
lean_mark_persistent(l_Lean_Meta_State_inhabited);
l_Lean_Meta_Lean_MonadError___closed__1 = _init_l_Lean_Meta_Lean_MonadError___closed__1();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__1);
l_Lean_Meta_Lean_MonadError___closed__2 = _init_l_Lean_Meta_Lean_MonadError___closed__2();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__2);
l_Lean_Meta_Lean_MonadError___closed__3 = _init_l_Lean_Meta_Lean_MonadError___closed__3();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__3);
l_Lean_Meta_Lean_MonadError___closed__4 = _init_l_Lean_Meta_Lean_MonadError___closed__4();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__4);
l_Lean_Meta_Lean_MonadError___closed__5 = _init_l_Lean_Meta_Lean_MonadError___closed__5();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__5);
l_Lean_Meta_Lean_MonadError___closed__6 = _init_l_Lean_Meta_Lean_MonadError___closed__6();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError___closed__6);
l_Lean_Meta_Lean_MonadError = _init_l_Lean_Meta_Lean_MonadError();
lean_mark_persistent(l_Lean_Meta_Lean_MonadError);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__1);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__2);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__3);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__5);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__6);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7 = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__7);
l_Lean_Meta_Lean_SimpleMonadTracerAdapter = _init_l_Lean_Meta_Lean_SimpleMonadTracerAdapter();
lean_mark_persistent(l_Lean_Meta_Lean_SimpleMonadTracerAdapter);
l_Lean_Meta_MetaM_run_x27___rarg___closed__1 = _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_MetaM_run_x27___rarg___closed__1);
l_Lean_Meta_MetaM_run_x27___rarg___closed__2 = _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_MetaM_run_x27___rarg___closed__2);
l_Lean_Meta_MetaM_run_x27___rarg___closed__3 = _init_l_Lean_Meta_MetaM_run_x27___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_MetaM_run_x27___rarg___closed__3);
l_Lean_Meta_hasEval___rarg___closed__1 = _init_l_Lean_Meta_hasEval___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_hasEval___rarg___closed__1);
l_Lean_Meta_hasEval___rarg___closed__2 = _init_l_Lean_Meta_hasEval___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_hasEval___rarg___closed__2);
l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1 = _init_l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1);
l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1 = _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_1__regTraceClasses___closed__1);
l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2 = _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2);
l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3 = _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_1__regTraceClasses___closed__3);
l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4 = _init_l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4);
res = l___private_Lean_Meta_Basic_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_getLCtx___rarg___closed__1 = _init_l_Lean_Meta_getLCtx___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getLCtx___rarg___closed__1);
l_Lean_Meta_getLCtx___rarg___closed__2 = _init_l_Lean_Meta_getLCtx___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getLCtx___rarg___closed__2);
l_Lean_Meta_getLCtx___rarg___closed__3 = _init_l_Lean_Meta_getLCtx___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_getLCtx___rarg___closed__3);
l_Lean_Meta_getLocalInstances___rarg___closed__1 = _init_l_Lean_Meta_getLocalInstances___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getLocalInstances___rarg___closed__1);
l_Lean_Meta_getLocalInstances___rarg___closed__2 = _init_l_Lean_Meta_getLocalInstances___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getLocalInstances___rarg___closed__2);
l_Lean_Meta_getConfig___rarg___closed__1 = _init_l_Lean_Meta_getConfig___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getConfig___rarg___closed__1);
l_Lean_Meta_getConfig___rarg___closed__2 = _init_l_Lean_Meta_getConfig___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getConfig___rarg___closed__2);
l_Lean_Meta_getMCtx___rarg___closed__1 = _init_l_Lean_Meta_getMCtx___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getMCtx___rarg___closed__1);
l_Lean_Meta_getMCtx___rarg___closed__2 = _init_l_Lean_Meta_getMCtx___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getMCtx___rarg___closed__2);
l_Lean_Meta_getMCtx___rarg___closed__3 = _init_l_Lean_Meta_getMCtx___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_getMCtx___rarg___closed__3);
l_Lean_Meta_getMCtx___rarg___closed__4 = _init_l_Lean_Meta_getMCtx___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_getMCtx___rarg___closed__4);
l_Lean_Meta_mkWHNFRef___lambda__1___closed__1 = _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkWHNFRef___lambda__1___closed__1);
l_Lean_Meta_mkWHNFRef___lambda__1___closed__2 = _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkWHNFRef___lambda__1___closed__2);
l_Lean_Meta_mkWHNFRef___lambda__1___closed__3 = _init_l_Lean_Meta_mkWHNFRef___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkWHNFRef___lambda__1___closed__3);
l_Lean_Meta_mkWHNFRef___closed__1 = _init_l_Lean_Meta_mkWHNFRef___closed__1();
lean_mark_persistent(l_Lean_Meta_mkWHNFRef___closed__1);
res = l_Lean_Meta_mkWHNFRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_whnfRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_whnfRef);
lean_dec_ref(res);
l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1 = _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkInferTypeRef___lambda__1___closed__1);
l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2 = _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkInferTypeRef___lambda__1___closed__2);
l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3 = _init_l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkInferTypeRef___lambda__1___closed__3);
l_Lean_Meta_mkInferTypeRef___closed__1 = _init_l_Lean_Meta_mkInferTypeRef___closed__1();
lean_mark_persistent(l_Lean_Meta_mkInferTypeRef___closed__1);
res = l_Lean_Meta_mkInferTypeRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_inferTypeRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_inferTypeRef);
lean_dec_ref(res);
l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1 = _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__1);
l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2 = _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__2);
l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3 = _init_l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkIsExprDefEqAuxRef___lambda__1___closed__3);
l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1 = _init_l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1();
lean_mark_persistent(l_Lean_Meta_mkIsExprDefEqAuxRef___closed__1);
res = l_Lean_Meta_mkIsExprDefEqAuxRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_isExprDefEqAuxRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_isExprDefEqAuxRef);
lean_dec_ref(res);
l_Lean_Meta_mkSynthPendingRef___closed__1 = _init_l_Lean_Meta_mkSynthPendingRef___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSynthPendingRef___closed__1);
res = l_Lean_Meta_mkSynthPendingRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthPendingRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthPendingRef);
lean_dec_ref(res);
l_Lean_Meta_whnf___rarg___closed__1 = _init_l_Lean_Meta_whnf___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_whnf___rarg___closed__1);
l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1 = _init_l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFreshExprMVarAt___rarg___closed__1);
l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1 = _init_l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFreshLevelMVar___rarg___closed__1);
l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2 = _init_l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkFreshLevelMVar___rarg___closed__2);
l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1 = _init_l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFreshTypeMVar___rarg___closed__1);
l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1 = _init_l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1);
l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1 = _init_l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__1);
l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2 = _init_l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_shouldReduceReducibleOnly___rarg___closed__2);
l_Lean_Meta_getTransparency___rarg___closed__1 = _init_l_Lean_Meta_getTransparency___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getTransparency___rarg___closed__1);
l_Lean_Meta_getTransparency___rarg___closed__2 = _init_l_Lean_Meta_getTransparency___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getTransparency___rarg___closed__2);
l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__1);
l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2);
l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3);
l_Lean_Meta_getMVarDecl___rarg___closed__1 = _init_l_Lean_Meta_getMVarDecl___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___rarg___closed__1);
l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1 = _init_l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_isReadOnlyExprMVar___rarg___closed__1);
l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1 = _init_l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___rarg___closed__1);
l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__1);
l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__2);
l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_isReadOnlyLevelMVar___rarg___lambda__1___closed__3);
l_Lean_Meta_throwUnknownFVar___rarg___closed__1 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__1);
l_Lean_Meta_throwUnknownFVar___rarg___closed__2 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__2);
l_Lean_Meta_throwUnknownFVar___rarg___closed__3 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__3);
l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1 = _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__1);
l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2 = _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__2);
l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3 = _init_l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3);
l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1 = _init_l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1);
l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1 = _init_l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__1);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__4);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__5);
l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6 = _init_l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__6);
l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_withNewLocalInstances___rarg___lambda__1___closed__1);
l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1 = _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__1);
l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2 = _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_Meta_getParamNamesImpl___spec__3___closed__2);
l_Lean_Meta_getParamNamesImpl___closed__1 = _init_l_Lean_Meta_getParamNamesImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_getParamNamesImpl___closed__1);
l_Lean_Meta_normalizeLevel___rarg___closed__1 = _init_l_Lean_Meta_normalizeLevel___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_normalizeLevel___rarg___closed__1);
l_Lean_Meta_setInlineAttribute___rarg___closed__1 = _init_l_Lean_Meta_setInlineAttribute___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_setInlineAttribute___rarg___closed__1);
l_Lean_Meta_setInlineAttribute___rarg___closed__2 = _init_l_Lean_Meta_setInlineAttribute___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_setInlineAttribute___rarg___closed__2);
l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1 = _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__1);
l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2 = _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__2);
l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3 = _init_l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Basic_34__instantiateForallAux___main___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
