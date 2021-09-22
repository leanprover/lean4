// Lean compiler output
// Module: Lean.Meta.Basic
// Imports: Init Lean.Data.LOption Lean.Environment Lean.Class Lean.ReducibilityAttrs Lean.Util.Trace Lean.Util.RecDepth Lean.Util.PPExt Lean.Util.OccursCheck Lean.Util.MonadBacktrack Lean.Compiler.InlineAttrs Lean.Meta.TransparencyMode Lean.Meta.DiscrTreeTypes Lean.Eval Lean.CoreM
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
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqInfoCacheKey;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_synthInstance___default;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_transparency___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedParamInfo___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_ignoreLevelMVarDepth___default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedState___closed__4;
LEAN_EXPORT uint8_t l_Lean_Meta_Config_zetaNonDep___default;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_binderInfo___default;
uint8_t l_USize_decEq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3;
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__10;
static lean_object* l_Lean_Meta_instMonadMetaM___closed__2;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkFunUnit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run(lean_object*);
extern lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isInstImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapError(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMonadMetaM___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_restore(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instOrElseMetaM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_occursCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1;
lean_object* l_Lean_MetavarContext_getExprAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_MetavarContext_isDelayedAssigned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_State_postponed___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_State_mctx___default;
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimMVarDeps(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarKind(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_getParamNames___closed__1;
lean_object* l_instInhabitedDepArrow___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVarsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarWithId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkFunUnit___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___boxed(lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_State_zetaFVarIds___default;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLevelMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_funInfo___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedPostponedEntry;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_unificationHints___default;
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg___boxed(lean_object*, lean_object*);
static size_t l_Lean_Meta_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_instAlternativeMetaM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_setInlineAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDelayedAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshTypeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cache_synthInstance___default___closed__1;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD(lean_object*);
static lean_object* l_Lean_Meta_Context_lctx___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instAlternativeMetaM___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssigned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__11;
static lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCache;
extern lean_object* l_Lean_Compiler_inlineAttrs;
static lean_object* l_Lean_Meta_State_postponed___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_assignSyntheticOpaque___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_isDefEqStuckEx___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__3;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_218____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar(lean_object*);
static lean_object* l_Lean_Meta_State_postponed___default___closed__2;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Context_synthPendingDepth___default;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_toIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cache_inferType___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadBacktrackSavedStateMetaM;
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getLevelMVarDepth___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_offsetCnstrs___default;
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
static lean_object* l_Lean_Meta_mkArrow___closed__2;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_defEqDefault___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_renameMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevelMVarDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4;
static lean_object* l_Lean_Meta_instMonadMetaM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
static lean_object* l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2;
static lean_object* l_Lean_Meta_instAddMessageContextMetaM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_liftMetaM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVarDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_renameMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__8;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_hasFwdDeps___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSavedState;
static lean_object* l_Lean_Meta_mkFunUnit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run_x27(lean_object*);
static lean_object* l_Lean_Meta_Cache_defEqDefault___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__1;
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__9;
LEAN_EXPORT uint8_t l_Lean_Meta_Config_constApprox___default;
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process(lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_whnfAll___default;
static lean_object* l_Lean_Meta_getLevelMVarDepth___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM(lean_object*);
lean_object* l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Lean_Meta_Config_ctxApprox___default;
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_dependsOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_Meta_instInhabitedSavedState___closed__4;
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_State_cache___default;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__1;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_backDeps___default;
LEAN_EXPORT uint8_t l_Lean_Meta_Config_quasiPatternApprox___default;
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_liftMetaM(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instAlternativeMetaM___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_instMonadMetaM___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp(lean_object*);
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaBoundedTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getLevelMVarDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescopeReducing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297_(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Context_lctx___default___closed__2;
static lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_occursCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
static lean_object* l_Lean_Meta_mkArrow___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthPending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCache___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedParamInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVarsFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Context_config___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVarDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isDelayedAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInfoCacheKey;
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceReducibleOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_foApprox___default;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth(lean_object*);
static lean_object* l_Lean_Meta_Cache_defEqDefault___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_State_mctx___default___closed__1;
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_paramInfo___default;
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_resultDeps___default;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqInfoCacheKey___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapErrorImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedMetaM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM;
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownFVar___rarg___closed__2;
lean_object* l_Lean_MetavarContext_addExprMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instOrElseMetaM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignLevel(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MetaM_toIO___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Context_lctx___default;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_trackZeta___default;
static lean_object* l_Lean_Meta_State_postponed___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cache_funInfo___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getTheoremInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2;
static lean_object* l_Lean_Meta_instInhabitedMetaM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx(lean_object*);
static lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getTransparency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_restoreSynthInstanceCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedInfoCacheKey___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_isDelayedAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Context_config___default___closed__1;
static lean_object* l_Lean_Meta_instInhabitedPostponedEntry___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedState;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Cache_inferType___default___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Meta_instMonadMetaM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedInfoCacheKey___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_defEqAll___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_whnfDefault___default;
static lean_object* l_Lean_Meta_Cache_defEqDefault___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances(lean_object*);
static lean_object* l_Lean_Meta_State_mctx___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_occursCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnumAttributes_setValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_instInhabitedInfoCacheKey___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Context_localInstances___default;
LEAN_EXPORT lean_object* l_Lean_Meta_getTheoremInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cache_funInfo___default___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadLCtxMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Context_defEqCtx_x3f___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDeclFromUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSavedState___closed__7;
static lean_object* l_Lean_Meta_getLocalDeclFromUserName___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cache_inferType___default___closed__3;
static lean_object* l_Lean_Meta_getLocalDeclFromUserName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isStrictImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_orElse(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Config_proofIrrelevance___default;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Cache_inferType___default;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedPostponedEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sortFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg(size_t, size_t, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instAddMessageContextMetaM;
LEAN_EXPORT lean_object* l_Lean_Meta_mapError___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadLCtxMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignableMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyInferTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_3_(lean_object* x_1) {
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
static uint8_t _init_l_Lean_Meta_Config_proofIrrelevance___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_assignSyntheticOpaque___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_ignoreLevelMVarDepth___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Config_offsetCnstrs___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_ParamInfo_binderInfo___default() {
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
static lean_object* _init_l_Lean_Meta_ParamInfo_backDeps___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ParamInfo_backDeps___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedParamInfo___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 0;
x_3 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_4 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
return x_4;
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
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = 1;
x_4 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_ParamInfo_isImplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = 3;
x_4 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isInstImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_ParamInfo_isInstImplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = 2;
x_4 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isStrictImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_ParamInfo_isStrictImplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = 0;
x_4 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = 4;
x_6 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_2, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ParamInfo_isExplicit___boxed(lean_object* x_1) {
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
x_1 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_FunInfo_resultDeps___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
return x_1;
}
}
static uint64_t _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_instInhabitedInfoCacheKey___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Meta_instInhabitedInfoCacheKey___closed__2;
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
x_1 = l_Lean_Meta_instInhabitedInfoCacheKey___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_3, x_6);
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
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1(x_5, x_8);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_297____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_6 = l_Lean_Expr_hash(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_mix_hash(x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_uint64_of_nat(x_10);
x_12 = 13;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_mix_hash(x_6, x_13);
x_15 = lean_uint64_mix_hash(x_5, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_inferType___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_inferType___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cache_inferType___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
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
x_1 = l_Lean_Meta_Cache_inferType___default___closed__3;
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
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
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
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
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
x_1 = l_Lean_Meta_Cache_inferType___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_whnfAll___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_defEqDefault___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cache_defEqDefault___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cache_defEqDefault___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cache_defEqDefault___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_defEqDefault___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cache_defEqAll___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Cache_defEqDefault___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__3;
x_2 = l_Lean_Meta_Cache_funInfo___default___closed__2;
x_3 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
x_4 = l_Lean_Meta_instInhabitedCache___closed__1;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCache___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedPostponedEntry___closed__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedInfoCacheKey___closed__1;
x_2 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint64(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedPostponedEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_instInhabitedPostponedEntry___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedPostponedEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedPostponedEntry___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_mctx___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_State_mctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_State_mctx___default___closed__1;
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_State_mctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_State_mctx___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_cache___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCache___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_zetaFVarIds___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_State_postponed___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_State_postponed___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_State_postponed___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_State_postponed___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_State_postponed___default___closed__2;
x_3 = l_Lean_Meta_State_postponed___default___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_State_postponed___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_State_postponed___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instInhabitedState___closed__1;
x_2 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_instInhabitedState___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_State_mctx___default___closed__2;
x_3 = l_Lean_Meta_instInhabitedCache___closed__2;
x_4 = l_Lean_Meta_instInhabitedState___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedState___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_3 = l_Lean_Meta_instInhabitedSavedState___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static uint32_t _init_l_Lean_Meta_instInhabitedSavedState___closed__4() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__5() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instInhabitedSavedState___closed__4;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_5 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_2 = l_Lean_Meta_instInhabitedSavedState___closed__3;
x_3 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_4 = l_Lean_Meta_instInhabitedSavedState___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Meta_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instInhabitedSavedState___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_instInhabitedSavedState___closed__7;
x_4 = l_Lean_Meta_instInhabitedSavedState___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_State_mctx___default___closed__2;
x_3 = l_Lean_Meta_instInhabitedCache___closed__2;
x_4 = l_Lean_Meta_instInhabitedState___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSavedState___closed__9;
x_2 = l_Lean_Meta_instInhabitedSavedState___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSavedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSavedState___closed__11;
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
x_4 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_1);
lean_ctor_set_uint8(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, 5, x_2);
lean_ctor_set_uint8(x_4, 6, x_3);
lean_ctor_set_uint8(x_4, 7, x_1);
lean_ctor_set_uint8(x_4, 8, x_3);
lean_ctor_set_uint8(x_4, 9, x_3);
lean_ctor_set_uint8(x_4, 10, x_1);
lean_ctor_set_uint8(x_4, 11, x_3);
lean_ctor_set_uint8(x_4, 12, x_3);
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
static lean_object* _init_l_Lean_Meta_Context_lctx___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cache_inferType___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Context_lctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Context_lctx___default___closed__1;
x_2 = l_Lean_Meta_State_postponed___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Context_lctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Context_lctx___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_localInstances___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_defEqCtx_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Context_synthPendingDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_6(x_4, x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lambda__2), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_Meta_instMonadMetaM___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = l_Lean_Meta_instMonadMetaM___closed__3;
lean_ctor_set(x_2, 1, x_5);
x_6 = l_Lean_Meta_instMonadMetaM___closed__4;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = l_Lean_Meta_instMonadMetaM___closed__3;
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
x_14 = l_Lean_Meta_instMonadMetaM___closed__4;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_instMonadMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instMonadMetaM___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMetaM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instMonadMetaM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedMetaM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedMetaM___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instInhabitedMetaM___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadLCtxMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadLCtxMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_instMonadLCtxMetaM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
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
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = l_Lean_Meta_instMonadMCtxMetaM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_instMonadMCtxMetaM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instMonadMCtxMetaM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_get(x_3, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_saveState___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_saveState___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_saveState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Core_restore(x_7, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 2);
x_19 = lean_ctor_get(x_13, 3);
x_20 = lean_ctor_get(x_14, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_ctor_set(x_14, 3, x_19);
lean_ctor_set(x_14, 2, x_18);
lean_ctor_set(x_14, 0, x_17);
x_23 = lean_st_ref_set(x_3, x_14, x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 2);
x_32 = lean_ctor_get(x_13, 3);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
x_35 = lean_st_ref_set(x_3, x_34, x_15);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SavedState_restore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_saveState___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SavedState_restore___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1;
x_2 = l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MetaM_toIO___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception #");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_8);
x_12 = lean_st_mk_ref(x_3, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_mk_ref(x_5, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_18);
x_20 = lean_apply_5(x_1, x_4, x_18, x_2, x_13, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_13, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_18, x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_13, x_27);
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_18);
lean_dec(x_13);
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_MessageData_toString(x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_20, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_inc(x_55);
lean_dec(x_38);
x_56 = l_Nat_repr(x_55);
x_57 = l_Lean_Meta_MetaM_toIO___rarg___closed__1;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_20, 0, x_59);
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_ctor_get(x_38, 0);
lean_inc(x_61);
lean_dec(x_38);
x_62 = l_Nat_repr(x_61);
x_63 = l_Lean_Meta_MetaM_toIO___rarg___closed__1;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_2, 2);
x_70 = lean_ctor_get(x_2, 3);
x_71 = lean_ctor_get(x_2, 4);
x_72 = lean_ctor_get(x_2, 5);
x_73 = lean_ctor_get(x_2, 7);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 4, x_71);
lean_ctor_set(x_74, 5, x_72);
lean_ctor_set(x_74, 6, x_8);
lean_ctor_set(x_74, 7, x_73);
x_75 = lean_st_mk_ref(x_3, x_9);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_get(x_76, x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_mk_ref(x_5, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_76);
lean_inc(x_81);
x_83 = lean_apply_5(x_1, x_4, x_81, x_74, x_76, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_76, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_get(x_81, x_87);
lean_dec(x_81);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_76, x_90);
lean_dec(x_76);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_89);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_81);
lean_dec(x_76);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
lean_dec(x_83);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_MessageData_toString(x_100, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
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
x_105 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_105, 0, x_102);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_104;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_ctor_get(x_83, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_112 = x_83;
} else {
 lean_dec_ref(x_83);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_98, 0);
lean_inc(x_113);
lean_dec(x_98);
x_114 = l_Nat_repr(x_113);
x_115 = l_Lean_Meta_MetaM_toIO___rarg___closed__1;
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_112;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_111);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
return x_7;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_7, 0);
x_121 = lean_ctor_get(x_7, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_7);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_toIO(lean_object* x_1) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Context_config___default___closed__1;
x_3 = l_Lean_Meta_Context_lctx___default___closed__2;
x_4 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_State_mctx___default___closed__2;
x_3 = l_Lean_Meta_instInhabitedCache___closed__2;
x_4 = l_Lean_Meta_State_postponed___default___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_uniq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Meta_State_postponed___default___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_218____spec__1(x_3, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Core_getMaxHeartbeats(x_3);
x_33 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3;
x_34 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6;
x_35 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7;
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_io_get_num_heartbeats(x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
x_47 = lean_st_ref_get(x_45, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2;
x_50 = lean_st_mk_ref(x_49, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1;
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_51);
x_54 = lean_apply_5(x_4, x_53, x_51, x_43, x_45, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_45, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_get(x_51, x_58);
lean_dec(x_51);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_45);
x_61 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_43, x_45, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_45, x_62);
lean_dec(x_45);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_apply_5(x_1, x_66, x_3, x_55, x_68, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_55);
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_1);
x_70 = lean_ctor_get(x_61, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_dec(x_61);
x_7 = x_70;
x_8 = x_71;
goto block_28;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_54, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
lean_dec(x_54);
x_74 = l_Lean_printTraces___at_Lean_Core_instMetaEvalCoreM___spec__1(x_43, x_45, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_7 = x_72;
x_8 = x_75;
goto block_28;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_72);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_7 = x_76;
x_8 = x_77;
goto block_28;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_37);
if (x_78 == 0)
{
return x_37;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_37, 0);
x_80 = lean_ctor_get(x_37, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_37);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
x_24 = l_Lean_Meta_MetaM_toIO___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instMetaEvalMetaM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instMetaEvalMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_throwIsDefEqStuck___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIsDefEqStuck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_liftMetaM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftMetaM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_liftMetaM___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mapMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mapMetaM___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_1, x_3);
x_10 = lean_apply_7(x_2, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_map1MetaM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_map1MetaM___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_3, x_4);
x_11 = lean_apply_7(x_2, lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_map2MetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_map2MetaM___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_modifyCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_10, 1, x_14);
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
x_26 = lean_apply_1(x_1, x_23);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
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
LEAN_EXPORT lean_object* l_Lean_Meta_modifyCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_modifyCache(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_modifyInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_apply_1(x_1, x_16);
lean_ctor_set(x_11, 0, x_17);
x_18 = lean_st_ref_set(x_3, x_10, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 2);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_ctor_get(x_11, 5);
x_31 = lean_ctor_get(x_11, 6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_32 = lean_apply_1(x_1, x_25);
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_33, 6, x_31);
lean_ctor_set(x_10, 1, x_33);
x_34 = lean_st_ref_set(x_3, x_10, x_12);
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
x_37 = lean_box(0);
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
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 2);
x_41 = lean_ctor_get(x_10, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_11, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_11, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_49 = x_11;
} else {
 lean_dec_ref(x_11);
 x_49 = lean_box(0);
}
x_50 = lean_apply_1(x_1, x_42);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
x_53 = lean_st_ref_set(x_3, x_52, x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_modifyInferTypeCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_modifyInferTypeCache(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = lean_box(0);
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
x_23 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resetZetaFVarIds___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_resetZetaFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_resetZetaFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getZetaFVarIds___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getZetaFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getZetaFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getPostponed___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getPostponed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getPostponed(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_modifyPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_modifyPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthPending___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_synth_pending(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withIncRecDepth___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarAtCore(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = l_Lean_mkFreshMVarId___at_Lean_Meta_mkFreshExprMVarAt___spec__1(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_4, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_7);
x_16 = l_Lean_MetavarContext_addLevelMVarDecl(x_15, x_7);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_2, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_mkLevelMVar(x_7);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_mkLevelMVar(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
lean_inc(x_7);
x_28 = l_Lean_MetavarContext_addLevelMVarDecl(x_24, x_7);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_st_ref_set(x_2, x_29, x_13);
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
x_33 = l_Lean_mkLevelMVar(x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkFreshLevelMVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Meta_mkFreshLevelMVar(x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshTypeMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprMVarWithId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_12;
x_3 = x_16;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1(x_1, x_1, x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at_Lean_Meta_mkFreshLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVarsFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ConstantInfo_numLevelParams(x_1);
x_8 = l_Lean_Meta_mkFreshLevelMVars(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshLevelMVarsFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkFreshLevelMVarsFor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2(x_19, x_2, x_3, x_4, x_5, x_10);
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
x_29 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2(x_32, x_2, x_3, x_4, x_5, x_23);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_mkFreshLevelMVarsFor(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkConst(x_1, x_12);
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
x_16 = l_Lean_mkConst(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getTransparency(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getTransparency___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_10, x_9);
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
x_17 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_16, x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceReducibleOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_10, x_9);
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
x_17 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_16, x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_shouldReduceReducibleOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = lean_mk_string("unknown metavariable '?");
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_1);
x_14 = l_Lean_MetavarContext_findDecl_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_9);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Meta_getMVarDecl___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(x_19, x_2, x_3, x_4, x_5, x_12);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_MetavarContext_findDecl_x3f(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_Meta_getMVarDecl___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1(x_30, x_2, x_3, x_4, x_5, x_23);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarKind(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_8);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, 10);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_st_ref_get(x_5, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_8, 3);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; 
x_41 = 1;
x_42 = lean_box(x_41);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
uint8_t x_43; lean_object* x_44; 
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
lean_dec(x_8);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_7);
if (x_57 == 0)
{
return x_7;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_getLevelMVarDepth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe metavariable '?");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getLevelMVarDepth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getLevelMVarDepth___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevelMVarDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_1);
x_14 = l_Lean_MetavarContext_findLevelDepth_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_9);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Meta_getLevelMVarDepth___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(x_19, x_2, x_3, x_4, x_5, x_12);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_MetavarContext_findLevelDepth_x3f(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_Meta_getLevelMVarDepth___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(x_30, x_2, x_3, x_4, x_5, x_23);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevelMVarDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLevelMVarDepth(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, 11);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_getLevelMVarDepth(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_3, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_nat_dec_eq(x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_nat_dec_eq(x_12, x_29);
lean_dec(x_29);
lean_dec(x_12);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
lean_dec(x_42);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_7, 0, x_44);
return x_7;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_dec(x_7);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_renameMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_renameMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isExprMVarAssigned(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getExprMVarAssignment_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_occursCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isDelayedAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isDelayedAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isDelayedAssigned(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDelayedAssignment_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getDelayedAssignment_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_hasAssignableMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwUnknownFVar___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownFVar___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownFVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_fvarId_x21(x_1);
x_8 = l_Lean_Meta_getLocalDecl(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getLocalDeclFromUserName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getLocalDeclFromUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_level_update_succ(x_1, x_11);
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
x_15 = lean_level_update_succ(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_17);
x_19 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_17, x_2, x_3, x_4, x_5, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set_uint64(x_23, sizeof(void*)*1, x_18);
x_24 = lean_level_update_succ(x_23, x_20);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
case 2:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_29 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_27, x_2, x_3, x_4, x_5, x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_28);
x_32 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_28, x_2, x_3, x_4, x_5, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_level_update_max(x_1, x_30, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_level_update_max(x_1, x_30, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
lean_inc(x_40);
x_43 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_40, x_2, x_3, x_4, x_5, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_41);
x_46 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_41, x_2, x_3, x_4, x_5, x_45);
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
x_50 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set_uint64(x_50, sizeof(void*)*2, x_42);
x_51 = lean_level_update_max(x_50, x_44, x_47);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
case 3:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_56 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_54, x_2, x_3, x_4, x_5, x_6);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_55);
x_59 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_55, x_2, x_3, x_4, x_5, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_level_update_imax(x_1, x_57, x_61);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_level_update_imax(x_1, x_57, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
x_69 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
lean_inc(x_67);
x_70 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_67, x_2, x_3, x_4, x_5, x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_68);
x_73 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_68, x_2, x_3, x_4, x_5, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set_uint64(x_77, sizeof(void*)*2, x_69);
x_78 = lean_level_update_imax(x_77, x_71, x_74);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
case 5:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_st_ref_get(x_5, x_6);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_get(x_3, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_80);
x_88 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_87, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_80);
lean_ctor_set(x_83, 0, x_1);
return x_83;
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Level_hasMVar(x_89);
if (x_90 == 0)
{
lean_dec(x_80);
lean_ctor_set(x_83, 0, x_89);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_free_object(x_83);
x_91 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_89, x_2, x_3, x_4, x_5, x_86);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_get(x_5, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_take(x_3, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_92);
x_101 = l_Lean_MetavarContext_assignLevel(x_100, x_80, x_92);
lean_ctor_set(x_97, 0, x_101);
x_102 = lean_st_ref_set(x_3, x_97, x_98);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_92);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = lean_ctor_get(x_97, 1);
x_109 = lean_ctor_get(x_97, 2);
x_110 = lean_ctor_get(x_97, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_97);
lean_inc(x_92);
x_111 = l_Lean_MetavarContext_assignLevel(x_107, x_80, x_92);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_110);
x_113 = lean_st_ref_set(x_3, x_112, x_98);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_92);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_83, 0);
x_118 = lean_ctor_get(x_83, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_83);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_80);
x_120 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_119, x_80);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_dec(x_80);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; uint8_t x_123; 
lean_dec(x_1);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Level_hasMVar(x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_80);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_125 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_122, x_2, x_3, x_4, x_5, x_118);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_st_ref_get(x_5, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_3, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
lean_inc(x_126);
x_138 = l_Lean_MetavarContext_assignLevel(x_133, x_80, x_126);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
x_140 = lean_st_ref_set(x_3, x_139, x_132);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_126);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
default: 
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_6);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLevelMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateLevelMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_level_update_succ(x_1, x_12);
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
x_16 = lean_level_update_succ(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_18);
x_20 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_18, x_2, x_3, x_4, x_5, x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_19);
x_25 = lean_level_update_succ(x_24, x_21);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
case 2:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_30 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_28, x_2, x_3, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_29);
x_33 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_29, x_2, x_3, x_4, x_5, x_6, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_level_update_max(x_1, x_31, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_level_update_max(x_1, x_31, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_41);
x_44 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_41, x_2, x_3, x_4, x_5, x_6, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_42);
x_47 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_42, x_2, x_3, x_4, x_5, x_6, x_46);
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
x_51 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set_uint64(x_51, sizeof(void*)*2, x_43);
x_52 = lean_level_update_max(x_51, x_45, x_48);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
case 3:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_1);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_57 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_55, x_2, x_3, x_4, x_5, x_6, x_7);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_56);
x_60 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_56, x_2, x_3, x_4, x_5, x_6, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_level_update_imax(x_1, x_58, x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_level_update_imax(x_1, x_58, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_68 = lean_ctor_get(x_1, 0);
x_69 = lean_ctor_get(x_1, 1);
x_70 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_1);
lean_inc(x_68);
x_71 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_68, x_2, x_3, x_4, x_5, x_6, x_7);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_69);
x_74 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_69, x_2, x_3, x_4, x_5, x_6, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set_uint64(x_78, sizeof(void*)*2, x_70);
x_79 = lean_level_update_imax(x_78, x_72, x_75);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
case 5:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_st_ref_get(x_6, x_7);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_get(x_4, x_83);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_81);
x_89 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_88, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_dec(x_81);
lean_ctor_set(x_84, 0, x_1);
return x_84;
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_1);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Level_hasMVar(x_90);
if (x_91 == 0)
{
lean_dec(x_81);
lean_ctor_set(x_84, 0, x_90);
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_free_object(x_84);
x_92 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_90, x_2, x_3, x_4, x_5, x_6, x_87);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_6, x_94);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_st_ref_take(x_4, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_93);
x_102 = l_Lean_MetavarContext_assignLevel(x_101, x_81, x_93);
lean_ctor_set(x_98, 0, x_102);
x_103 = lean_st_ref_set(x_4, x_98, x_99);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set(x_103, 0, x_93);
return x_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_98, 0);
x_109 = lean_ctor_get(x_98, 1);
x_110 = lean_ctor_get(x_98, 2);
x_111 = lean_ctor_get(x_98, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_98);
lean_inc(x_93);
x_112 = l_Lean_MetavarContext_assignLevel(x_108, x_81, x_93);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
x_114 = lean_st_ref_set(x_4, x_113, x_99);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_93);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_84, 0);
x_119 = lean_ctor_get(x_84, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_84);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_81);
x_121 = l_Lean_MetavarContext_getLevelAssignment_x3f(x_120, x_81);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_dec(x_81);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_1);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Level_hasMVar(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_81);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_119);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_126 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_123, x_2, x_3, x_4, x_5, x_6, x_119);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_st_ref_get(x_6, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_take(x_4, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 3);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
lean_inc(x_127);
x_139 = l_Lean_MetavarContext_assignLevel(x_134, x_81, x_127);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 4, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
lean_ctor_set(x_140, 2, x_136);
lean_ctor_set(x_140, 3, x_137);
x_141 = lean_st_ref_set(x_4, x_140, x_133);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_127);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
default: 
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_7);
return x_145;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_12, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_23, x_3, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_27);
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
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_29);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_1);
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
static lean_object* _init_l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_1);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_15, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_free_object(x_13);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_35; lean_object* x_43; lean_object* x_44; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_59 = lean_st_ref_get(x_6, x_16);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_2, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_1);
x_64 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_62, x_1);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_st_ref_get(x_6, x_63);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_4, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_18);
x_71 = l_Lean_MetavarContext_getExprAssignment_x3f(x_70, x_18);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_43 = x_1;
x_44 = x_69;
goto block_58;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_73 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_72, x_2, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_6, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_take(x_4, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_74);
x_83 = l_Lean_MetavarContext_assignExpr(x_82, x_18, x_74);
lean_ctor_set(x_79, 0, x_83);
x_84 = lean_st_ref_set(x_4, x_79, x_80);
lean_dec(x_4);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_43 = x_74;
x_44 = x_85;
goto block_58;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
x_88 = lean_ctor_get(x_79, 2);
x_89 = lean_ctor_get(x_79, 3);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
lean_inc(x_74);
x_90 = l_Lean_MetavarContext_assignExpr(x_86, x_18, x_74);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_89);
x_92 = lean_st_ref_set(x_4, x_91, x_80);
lean_dec(x_4);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_43 = x_74;
x_44 = x_93;
goto block_58;
}
}
else
{
uint8_t x_94; 
lean_dec(x_18);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_73);
if (x_94 == 0)
{
x_35 = x_73;
goto block_42;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_73, 0);
x_96 = lean_ctor_get(x_73, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_73);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_35 = x_97;
goto block_42;
}
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_64, 0);
lean_inc(x_98);
lean_dec(x_64);
x_19 = x_98;
x_20 = x_63;
goto block_34;
}
block_34:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
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
x_26 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_27 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_19);
x_28 = l_Std_HashMap_insert___rarg(x_26, x_27, x_24, x_1, x_19);
x_29 = lean_st_ref_set(x_2, x_28, x_25);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_19);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_42:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_19 = x_36;
x_20 = x_37;
goto block_34;
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_58:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_st_ref_get(x_6, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_2, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_51 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_43);
lean_inc(x_1);
x_52 = l_Std_HashMap_insert___rarg(x_50, x_51, x_48, x_1, x_43);
x_53 = lean_st_ref_set(x_2, x_52, x_49);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_43);
x_35 = x_53;
goto block_42;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_56);
x_35 = x_57;
goto block_42;
}
}
}
case 3:
{
lean_object* x_99; uint64_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_99);
x_101 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_99, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set_uint64(x_104, sizeof(void*)*1, x_100);
x_105 = lean_expr_update_sort(x_104, x_102);
x_106 = lean_st_ref_get(x_6, x_103);
lean_dec(x_6);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_2, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_112 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_105);
x_113 = l_Std_HashMap_insert___rarg(x_111, x_112, x_109, x_1, x_105);
x_114 = lean_st_ref_set(x_2, x_113, x_110);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
lean_ctor_set(x_114, 0, x_105);
return x_114;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
case 4:
{
lean_object* x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_119 = lean_ctor_get(x_1, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
x_121 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_120);
x_122 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_8, x_120, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_120);
lean_ctor_set_uint64(x_125, sizeof(void*)*2, x_121);
x_126 = lean_expr_update_const(x_125, x_123);
x_127 = lean_st_ref_get(x_6, x_124);
lean_dec(x_6);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_2, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_133 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_126);
x_134 = l_Std_HashMap_insert___rarg(x_132, x_133, x_130, x_1, x_126);
x_135 = lean_st_ref_set(x_2, x_134, x_131);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_126);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
case 5:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_unsigned_to_nat(0u);
x_141 = l_Lean_Expr_getAppNumArgsAux(x_1, x_140);
x_142 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1;
lean_inc(x_141);
x_143 = lean_mk_array(x_141, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_sub(x_141, x_144);
lean_dec(x_141);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_146 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(x_8, x_1, x_143, x_145, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_st_ref_get(x_6, x_148);
lean_dec(x_6);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_2, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_155 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_147);
x_156 = l_Std_HashMap_insert___rarg(x_154, x_155, x_152, x_1, x_147);
x_157 = lean_st_ref_set(x_2, x_156, x_153);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_157, 0);
lean_dec(x_159);
lean_ctor_set(x_157, 0, x_147);
return x_157;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_147);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_146);
if (x_162 == 0)
{
return x_146;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_146, 0);
x_164 = lean_ctor_get(x_146, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_146);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
case 6:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint64_t x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 2);
lean_inc(x_168);
x_169 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_167);
x_170 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_167, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_168);
x_173 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_168, x_2, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_167);
lean_ctor_set(x_176, 2, x_168);
lean_ctor_set_uint64(x_176, sizeof(void*)*3, x_169);
x_177 = (uint8_t)((x_169 << 24) >> 61);
x_178 = lean_expr_update_lambda(x_176, x_177, x_171, x_174);
x_179 = lean_st_ref_get(x_6, x_175);
lean_dec(x_6);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_st_ref_take(x_2, x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_185 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_178);
x_186 = l_Std_HashMap_insert___rarg(x_184, x_185, x_182, x_1, x_178);
x_187 = lean_st_ref_set(x_2, x_186, x_183);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 0);
lean_dec(x_189);
lean_ctor_set(x_187, 0, x_178);
return x_187;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_178);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_173);
if (x_192 == 0)
{
return x_173;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_173, 0);
x_194 = lean_ctor_get(x_173, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_173);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_170);
if (x_196 == 0)
{
return x_170;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_170, 0);
x_198 = lean_ctor_get(x_170, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_170);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
case 7:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint64_t x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_1, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_1, 2);
lean_inc(x_202);
x_203 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_201);
x_204 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_201, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_202);
x_207 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_202, x_2, x_3, x_4, x_5, x_6, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_201);
lean_ctor_set(x_210, 2, x_202);
lean_ctor_set_uint64(x_210, sizeof(void*)*3, x_203);
x_211 = (uint8_t)((x_203 << 24) >> 61);
x_212 = lean_expr_update_forall(x_210, x_211, x_205, x_208);
x_213 = lean_st_ref_get(x_6, x_209);
lean_dec(x_6);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_st_ref_take(x_2, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_219 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_212);
x_220 = l_Std_HashMap_insert___rarg(x_218, x_219, x_216, x_1, x_212);
x_221 = lean_st_ref_set(x_2, x_220, x_217);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_dec(x_223);
lean_ctor_set(x_221, 0, x_212);
return x_221;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_212);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
else
{
uint8_t x_226; 
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_207);
if (x_226 == 0)
{
return x_207;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_207, 0);
x_228 = lean_ctor_get(x_207, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_207);
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
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_204);
if (x_230 == 0)
{
return x_204;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_204, 0);
x_232 = lean_ctor_get(x_204, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_204);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
case 8:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint64_t x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_1, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 3);
lean_inc(x_237);
x_238 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_235);
x_239 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_235, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_236);
x_242 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_236, x_2, x_3, x_4, x_5, x_6, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_237);
x_245 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_237, x_2, x_3, x_4, x_5, x_6, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_248, 0, x_234);
lean_ctor_set(x_248, 1, x_235);
lean_ctor_set(x_248, 2, x_236);
lean_ctor_set(x_248, 3, x_237);
lean_ctor_set_uint64(x_248, sizeof(void*)*4, x_238);
x_249 = lean_expr_update_let(x_248, x_240, x_243, x_246);
x_250 = lean_st_ref_get(x_6, x_247);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_st_ref_take(x_2, x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_256 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_249);
x_257 = l_Std_HashMap_insert___rarg(x_255, x_256, x_253, x_1, x_249);
x_258 = lean_st_ref_set(x_2, x_257, x_254);
lean_dec(x_2);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_258, 0);
lean_dec(x_260);
lean_ctor_set(x_258, 0, x_249);
return x_258;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_249);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
else
{
uint8_t x_263; 
lean_dec(x_243);
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_245);
if (x_263 == 0)
{
return x_245;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_245, 0);
x_265 = lean_ctor_get(x_245, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_245);
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
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_242);
if (x_267 == 0)
{
return x_242;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_242, 0);
x_269 = lean_ctor_get(x_242, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_242);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_239);
if (x_271 == 0)
{
return x_239;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_239, 0);
x_273 = lean_ctor_get(x_239, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_239);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
case 10:
{
lean_object* x_275; lean_object* x_276; uint64_t x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_1, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_1, 1);
lean_inc(x_276);
x_277 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_276);
x_278 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_276, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_281, 0, x_275);
lean_ctor_set(x_281, 1, x_276);
lean_ctor_set_uint64(x_281, sizeof(void*)*2, x_277);
x_282 = lean_expr_update_mdata(x_281, x_279);
x_283 = lean_st_ref_get(x_6, x_280);
lean_dec(x_6);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_st_ref_take(x_2, x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_289 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_282);
x_290 = l_Std_HashMap_insert___rarg(x_288, x_289, x_286, x_1, x_282);
x_291 = lean_st_ref_set(x_2, x_290, x_287);
lean_dec(x_2);
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_291, 0);
lean_dec(x_293);
lean_ctor_set(x_291, 0, x_282);
return x_291;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_282);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_278);
if (x_296 == 0)
{
return x_278;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_278, 0);
x_298 = lean_ctor_get(x_278, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_278);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
case 11:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint64_t x_303; lean_object* x_304; 
x_300 = lean_ctor_get(x_1, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_1, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_1, 2);
lean_inc(x_302);
x_303 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_302);
x_304 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_302, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_307, 0, x_300);
lean_ctor_set(x_307, 1, x_301);
lean_ctor_set(x_307, 2, x_302);
lean_ctor_set_uint64(x_307, sizeof(void*)*3, x_303);
x_308 = lean_expr_update_proj(x_307, x_305);
x_309 = lean_st_ref_get(x_6, x_306);
lean_dec(x_6);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_st_ref_take(x_2, x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_315 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_308);
x_316 = l_Std_HashMap_insert___rarg(x_314, x_315, x_312, x_1, x_308);
x_317 = lean_st_ref_set(x_2, x_316, x_313);
lean_dec(x_2);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_317, 0);
lean_dec(x_319);
lean_ctor_set(x_317, 0, x_308);
return x_317;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_308);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
else
{
uint8_t x_322; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_304);
if (x_322 == 0)
{
return x_304;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_304, 0);
x_324 = lean_ctor_get(x_304, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_304);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
default: 
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_326 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
x_328 = lean_st_ref_take(x_2, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_332 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc_n(x_1, 2);
x_333 = l_Std_HashMap_insert___rarg(x_331, x_332, x_329, x_1, x_1);
x_334 = lean_st_ref_set(x_2, x_333, x_330);
lean_dec(x_2);
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_334, 0);
lean_dec(x_336);
lean_ctor_set(x_334, 0, x_1);
return x_334;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_1);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
}
else
{
lean_object* x_339; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = lean_ctor_get(x_17, 0);
lean_inc(x_339);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_339);
return x_13;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_13, 0);
x_341 = lean_ctor_get(x_13, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_13);
lean_inc(x_1);
x_342 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_340, x_1);
if (lean_obj_tag(x_342) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_359; lean_object* x_367; lean_object* x_368; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_343 = lean_ctor_get(x_1, 0);
lean_inc(x_343);
x_382 = lean_st_ref_get(x_6, x_341);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_st_ref_get(x_2, x_383);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
lean_inc(x_1);
x_387 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_385, x_1);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_st_ref_get(x_6, x_386);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_st_ref_get(x_4, x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
lean_dec(x_391);
lean_inc(x_343);
x_394 = l_Lean_MetavarContext_getExprAssignment_x3f(x_393, x_343);
if (lean_obj_tag(x_394) == 0)
{
lean_dec(x_343);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_367 = x_1;
x_368 = x_392;
goto block_381;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec(x_394);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_396 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_395, x_2, x_3, x_4, x_5, x_6, x_392);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_st_ref_get(x_6, x_398);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = lean_st_ref_take(x_4, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_402, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_402, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 lean_ctor_release(x_402, 3);
 x_408 = x_402;
} else {
 lean_dec_ref(x_402);
 x_408 = lean_box(0);
}
lean_inc(x_397);
x_409 = l_Lean_MetavarContext_assignExpr(x_404, x_343, x_397);
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(0, 4, 0);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_405);
lean_ctor_set(x_410, 2, x_406);
lean_ctor_set(x_410, 3, x_407);
x_411 = lean_st_ref_set(x_4, x_410, x_403);
lean_dec(x_4);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
lean_dec(x_411);
x_367 = x_397;
x_368 = x_412;
goto block_381;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_343);
lean_dec(x_4);
x_413 = lean_ctor_get(x_396, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_396, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_415 = x_396;
} else {
 lean_dec_ref(x_396);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
x_359 = x_416;
goto block_366;
}
}
}
else
{
lean_object* x_417; 
lean_dec(x_343);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_417 = lean_ctor_get(x_387, 0);
lean_inc(x_417);
lean_dec(x_387);
x_344 = x_417;
x_345 = x_386;
goto block_358;
}
block_358:
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_346 = lean_st_ref_get(x_6, x_345);
lean_dec(x_6);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_348 = lean_st_ref_take(x_2, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_352 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_344);
x_353 = l_Std_HashMap_insert___rarg(x_351, x_352, x_349, x_1, x_344);
x_354 = lean_st_ref_set(x_2, x_353, x_350);
lean_dec(x_2);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_356 = x_354;
} else {
 lean_dec_ref(x_354);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_344);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
block_366:
{
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_344 = x_360;
x_345 = x_361;
goto block_358;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_364 = x_359;
} else {
 lean_dec_ref(x_359);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
block_381:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_369 = lean_st_ref_get(x_6, x_368);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_371 = lean_st_ref_take(x_2, x_370);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
x_374 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_375 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_367);
lean_inc(x_1);
x_376 = l_Std_HashMap_insert___rarg(x_374, x_375, x_372, x_1, x_367);
x_377 = lean_st_ref_set(x_2, x_376, x_373);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_367);
lean_ctor_set(x_380, 1, x_378);
x_359 = x_380;
goto block_366;
}
}
case 3:
{
lean_object* x_418; uint64_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_418 = lean_ctor_get(x_1, 0);
lean_inc(x_418);
x_419 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_418);
x_420 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_418, x_2, x_3, x_4, x_5, x_6, x_341);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set_uint64(x_423, sizeof(void*)*1, x_419);
x_424 = lean_expr_update_sort(x_423, x_421);
x_425 = lean_st_ref_get(x_6, x_422);
lean_dec(x_6);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_st_ref_take(x_2, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_431 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_424);
x_432 = l_Std_HashMap_insert___rarg(x_430, x_431, x_428, x_1, x_424);
x_433 = lean_st_ref_set(x_2, x_432, x_429);
lean_dec(x_2);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_424);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
case 4:
{
lean_object* x_437; lean_object* x_438; uint64_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_437 = lean_ctor_get(x_1, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_1, 1);
lean_inc(x_438);
x_439 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_438);
x_440 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_8, x_438, x_2, x_3, x_4, x_5, x_6, x_341);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set_uint64(x_443, sizeof(void*)*2, x_439);
x_444 = lean_expr_update_const(x_443, x_441);
x_445 = lean_st_ref_get(x_6, x_442);
lean_dec(x_6);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_st_ref_take(x_2, x_446);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_451 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_444);
x_452 = l_Std_HashMap_insert___rarg(x_450, x_451, x_448, x_1, x_444);
x_453 = lean_st_ref_set(x_2, x_452, x_449);
lean_dec(x_2);
x_454 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_455 = x_453;
} else {
 lean_dec_ref(x_453);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_444);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
case 5:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_457 = lean_unsigned_to_nat(0u);
x_458 = l_Lean_Expr_getAppNumArgsAux(x_1, x_457);
x_459 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1;
lean_inc(x_458);
x_460 = lean_mk_array(x_458, x_459);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_sub(x_458, x_461);
lean_dec(x_458);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_463 = l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5(x_8, x_1, x_460, x_462, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = lean_st_ref_get(x_6, x_465);
lean_dec(x_6);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = lean_st_ref_take(x_2, x_467);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_472 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_464);
x_473 = l_Std_HashMap_insert___rarg(x_471, x_472, x_469, x_1, x_464);
x_474 = lean_st_ref_set(x_2, x_473, x_470);
lean_dec(x_2);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_476 = x_474;
} else {
 lean_dec_ref(x_474);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_464);
lean_ctor_set(x_477, 1, x_475);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_478 = lean_ctor_get(x_463, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_463, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_480 = x_463;
} else {
 lean_dec_ref(x_463);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
}
case 6:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint64_t x_485; lean_object* x_486; 
x_482 = lean_ctor_get(x_1, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_1, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_1, 2);
lean_inc(x_484);
x_485 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_483);
x_486 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_483, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_484);
x_489 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_484, x_2, x_3, x_4, x_5, x_6, x_488);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
x_492 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_492, 0, x_482);
lean_ctor_set(x_492, 1, x_483);
lean_ctor_set(x_492, 2, x_484);
lean_ctor_set_uint64(x_492, sizeof(void*)*3, x_485);
x_493 = (uint8_t)((x_485 << 24) >> 61);
x_494 = lean_expr_update_lambda(x_492, x_493, x_487, x_490);
x_495 = lean_st_ref_get(x_6, x_491);
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
x_500 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_501 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_494);
x_502 = l_Std_HashMap_insert___rarg(x_500, x_501, x_498, x_1, x_494);
x_503 = lean_st_ref_set(x_2, x_502, x_499);
lean_dec(x_2);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_505 = x_503;
} else {
 lean_dec_ref(x_503);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_494);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_487);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_507 = lean_ctor_get(x_489, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_489, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_509 = x_489;
} else {
 lean_dec_ref(x_489);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_511 = lean_ctor_get(x_486, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_486, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_513 = x_486;
} else {
 lean_dec_ref(x_486);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
case 7:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; uint64_t x_518; lean_object* x_519; 
x_515 = lean_ctor_get(x_1, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_1, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_1, 2);
lean_inc(x_517);
x_518 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_516);
x_519 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_516, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_517);
x_522 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_517, x_2, x_3, x_4, x_5, x_6, x_521);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_525, 0, x_515);
lean_ctor_set(x_525, 1, x_516);
lean_ctor_set(x_525, 2, x_517);
lean_ctor_set_uint64(x_525, sizeof(void*)*3, x_518);
x_526 = (uint8_t)((x_518 << 24) >> 61);
x_527 = lean_expr_update_forall(x_525, x_526, x_520, x_523);
x_528 = lean_st_ref_get(x_6, x_524);
lean_dec(x_6);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_st_ref_take(x_2, x_529);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_534 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_527);
x_535 = l_Std_HashMap_insert___rarg(x_533, x_534, x_531, x_1, x_527);
x_536 = lean_st_ref_set(x_2, x_535, x_532);
lean_dec(x_2);
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_538 = x_536;
} else {
 lean_dec_ref(x_536);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_527);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_520);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_540 = lean_ctor_get(x_522, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_522, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_542 = x_522;
} else {
 lean_dec_ref(x_522);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_544 = lean_ctor_get(x_519, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_519, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_546 = x_519;
} else {
 lean_dec_ref(x_519);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
case 8:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint64_t x_552; lean_object* x_553; 
x_548 = lean_ctor_get(x_1, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_1, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_1, 2);
lean_inc(x_550);
x_551 = lean_ctor_get(x_1, 3);
lean_inc(x_551);
x_552 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_549);
x_553 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_549, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_550);
x_556 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_550, x_2, x_3, x_4, x_5, x_6, x_555);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_551);
x_559 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_551, x_2, x_3, x_4, x_5, x_6, x_558);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_562, 0, x_548);
lean_ctor_set(x_562, 1, x_549);
lean_ctor_set(x_562, 2, x_550);
lean_ctor_set(x_562, 3, x_551);
lean_ctor_set_uint64(x_562, sizeof(void*)*4, x_552);
x_563 = lean_expr_update_let(x_562, x_554, x_557, x_560);
x_564 = lean_st_ref_get(x_6, x_561);
lean_dec(x_6);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_566 = lean_st_ref_take(x_2, x_565);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_570 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_563);
x_571 = l_Std_HashMap_insert___rarg(x_569, x_570, x_567, x_1, x_563);
x_572 = lean_st_ref_set(x_2, x_571, x_568);
lean_dec(x_2);
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_574 = x_572;
} else {
 lean_dec_ref(x_572);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_563);
lean_ctor_set(x_575, 1, x_573);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_576 = lean_ctor_get(x_559, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_559, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_578 = x_559;
} else {
 lean_dec_ref(x_559);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_554);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_580 = lean_ctor_get(x_556, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_556, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_582 = x_556;
} else {
 lean_dec_ref(x_556);
 x_582 = lean_box(0);
}
if (lean_is_scalar(x_582)) {
 x_583 = lean_alloc_ctor(1, 2, 0);
} else {
 x_583 = x_582;
}
lean_ctor_set(x_583, 0, x_580);
lean_ctor_set(x_583, 1, x_581);
return x_583;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_584 = lean_ctor_get(x_553, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_553, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_586 = x_553;
} else {
 lean_dec_ref(x_553);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(1, 2, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
case 10:
{
lean_object* x_588; lean_object* x_589; uint64_t x_590; lean_object* x_591; 
x_588 = lean_ctor_get(x_1, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_1, 1);
lean_inc(x_589);
x_590 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_589);
x_591 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_589, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_594, 0, x_588);
lean_ctor_set(x_594, 1, x_589);
lean_ctor_set_uint64(x_594, sizeof(void*)*2, x_590);
x_595 = lean_expr_update_mdata(x_594, x_592);
x_596 = lean_st_ref_get(x_6, x_593);
lean_dec(x_6);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_598 = lean_st_ref_take(x_2, x_597);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_602 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_595);
x_603 = l_Std_HashMap_insert___rarg(x_601, x_602, x_599, x_1, x_595);
x_604 = lean_st_ref_set(x_2, x_603, x_600);
lean_dec(x_2);
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_606 = x_604;
} else {
 lean_dec_ref(x_604);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_595);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_608 = lean_ctor_get(x_591, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_591, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_610 = x_591;
} else {
 lean_dec_ref(x_591);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
case 11:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; uint64_t x_615; lean_object* x_616; 
x_612 = lean_ctor_get(x_1, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_1, 1);
lean_inc(x_613);
x_614 = lean_ctor_get(x_1, 2);
lean_inc(x_614);
x_615 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_614);
x_616 = l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1(x_614, x_2, x_3, x_4, x_5, x_6, x_341);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_619, 0, x_612);
lean_ctor_set(x_619, 1, x_613);
lean_ctor_set(x_619, 2, x_614);
lean_ctor_set_uint64(x_619, sizeof(void*)*3, x_615);
x_620 = lean_expr_update_proj(x_619, x_617);
x_621 = lean_st_ref_get(x_6, x_618);
lean_dec(x_6);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_623 = lean_st_ref_take(x_2, x_622);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_627 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_620);
x_628 = l_Std_HashMap_insert___rarg(x_626, x_627, x_624, x_1, x_620);
x_629 = lean_st_ref_set(x_2, x_628, x_625);
lean_dec(x_2);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_631 = x_629;
} else {
 lean_dec_ref(x_629);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_620);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_633 = lean_ctor_get(x_616, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_616, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_635 = x_616;
} else {
 lean_dec_ref(x_616);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
default: 
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_637 = lean_st_ref_get(x_6, x_341);
lean_dec(x_6);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
lean_dec(x_637);
x_639 = lean_st_ref_take(x_2, x_638);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_643 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc_n(x_1, 2);
x_644 = l_Std_HashMap_insert___rarg(x_642, x_643, x_640, x_1, x_1);
x_645 = lean_st_ref_set(x_2, x_644, x_641);
lean_dec(x_2);
x_646 = lean_ctor_get(x_645, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_647 = x_645;
} else {
 lean_dec_ref(x_645);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_1);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_649 = lean_ctor_get(x_342, 0);
lean_inc(x_649);
lean_dec(x_342);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_341);
return x_650;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_instInhabitedSavedState___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateMVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___at_Lean_Meta_instantiateMVars___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_instantiateMVars___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1(lean_object* x_1) {
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_18 = l_Lean_Meta_instInhabitedSavedState___closed__1;
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
x_60 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
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
x_68 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_69 = l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg(x_68, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_2);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_liftMkBindingM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_liftMkBindingM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_liftMkBindingM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_abstractRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = 0;
lean_inc(x_3);
x_22 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_3, x_1, x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_expr_abstract_range(x_23, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_st_ref_take(x_7, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_28, 2);
lean_dec(x_31);
lean_ctor_set(x_28, 2, x_26);
x_32 = lean_st_ref_set(x_7, x_28, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Meta_setMCtx(x_34, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_6);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_st_ref_set(x_7, x_43, x_29);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
lean_dec(x_24);
x_47 = l_Lean_Meta_setMCtx(x_46, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_6);
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
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = l_Lean_Meta_setMCtx(x_52, x_4, x_5, x_6, x_7, x_17);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_st_ref_take(x_7, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_57, 2);
lean_dec(x_60);
lean_ctor_set(x_57, 2, x_55);
x_61 = lean_st_ref_set(x_7, x_57, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_64 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_63, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_6);
lean_dec(x_4);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
x_67 = lean_ctor_get(x_57, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_st_ref_set(x_7, x_68, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_72 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_71, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_6);
lean_dec(x_4);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_abstractRange(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = l_Lean_Meta_abstractRange(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_abstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = 0;
x_25 = l_Lean_MetavarContext_MkBinding_mkBinding(x_24, x_11, x_1, x_2, x_3, x_4, x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_st_ref_take(x_8, x_20);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_31, 2);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_29);
x_35 = lean_st_ref_set(x_8, x_31, x_32);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Meta_setMCtx(x_37, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_28);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
x_45 = lean_ctor_get(x_31, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_29);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_st_ref_set(x_8, x_46, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
lean_dec(x_27);
x_50 = l_Lean_Meta_setMCtx(x_49, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_5);
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
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = l_Lean_Meta_setMCtx(x_55, x_5, x_6, x_7, x_8, x_20);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_st_ref_take(x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_60, 2);
lean_dec(x_63);
lean_ctor_set(x_60, 2, x_58);
x_64 = lean_st_ref_set(x_8, x_60, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_67 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_66, x_5, x_6, x_7, x_8, x_65);
lean_dec(x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
x_70 = lean_ctor_get(x_60, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_60);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_58);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_st_ref_set(x_8, x_71, x_61);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_75 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_74, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_5);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_5);
lean_dec(x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_9);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkLambdaFVars(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = 1;
x_25 = 0;
x_26 = l_Lean_MetavarContext_MkBinding_mkBinding(x_24, x_11, x_1, x_2, x_3, x_4, x_25, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_st_ref_take(x_8, x_20);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_32, 2);
lean_dec(x_35);
lean_ctor_set(x_32, 2, x_30);
x_36 = lean_st_ref_set(x_8, x_32, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_Meta_setMCtx(x_38, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_29);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
x_46 = lean_ctor_get(x_32, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_30);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_st_ref_set(x_8, x_47, x_33);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_28, 0);
lean_inc(x_50);
lean_dec(x_28);
x_51 = l_Lean_Meta_setMCtx(x_50, x_5, x_6, x_7, x_8, x_49);
lean_dec(x_5);
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
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_29);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = l_Lean_Meta_setMCtx(x_56, x_5, x_6, x_7, x_8, x_20);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_st_ref_take(x_8, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_61, 2);
lean_dec(x_64);
lean_ctor_set(x_61, 2, x_59);
x_65 = lean_st_ref_set(x_8, x_61, x_62);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_68 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_67, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
x_71 = lean_ctor_get(x_61, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_59);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_st_ref_set(x_8, x_72, x_62);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_76 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_75, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_5);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_5);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_9);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFVars(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkLetFVars(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_Meta_mkFunUnit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkFunUnit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkFunUnit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkFunUnit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkFunUnit___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_mkArrow___closed__2;
x_8 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_7, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = 0;
x_12 = l_Lean_Meta_mkFunUnit___closed__3;
x_13 = l_Lean_mkLambda(x_10, x_11, x_12, x_1);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = 0;
x_17 = l_Lean_Meta_mkFunUnit___closed__3;
x_18 = l_Lean_mkLambda(x_14, x_16, x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunUnit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkFunUnit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimMVarDeps(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_instInhabitedSavedState___closed__1;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_2, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_st_ref_take(x_7, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_27, 2);
lean_dec(x_30);
lean_ctor_set(x_27, 2, x_25);
x_31 = lean_st_ref_set(x_7, x_27, x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l_Lean_Meta_setMCtx(x_33, x_4, x_5, x_6, x_7, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
x_41 = lean_ctor_get(x_27, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_25);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_st_ref_set(x_7, x_42, x_28);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_24, 0);
lean_inc(x_45);
lean_dec(x_24);
x_46 = l_Lean_Meta_setMCtx(x_45, x_4, x_5, x_6, x_7, x_44);
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
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_dec(x_22);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = l_Lean_Meta_setMCtx(x_51, x_4, x_5, x_6, x_7, x_18);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_st_ref_take(x_7, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_56, 2);
lean_dec(x_59);
lean_ctor_set(x_56, 2, x_54);
x_60 = lean_st_ref_set(x_7, x_56, x_57);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_63 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_62, x_4, x_5, x_6, x_7, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
x_66 = lean_ctor_get(x_56, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_54);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_st_ref_set(x_7, x_67, x_57);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Meta_liftMkBindingM___rarg___closed__2;
x_71 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_70, x_4, x_5, x_6, x_7, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_2);
lean_ctor_set(x_72, 1, x_8);
return x_72;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimMVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_elimMVarDeps(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_18 = lean_apply_1(x_1, x_13);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
x_20 = lean_apply_7(x_3, lean_box(0), x_2, x_19, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withConfig___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get_uint8(x_9, 0);
x_14 = lean_ctor_get_uint8(x_9, 1);
x_15 = lean_ctor_get_uint8(x_9, 2);
x_16 = lean_ctor_get_uint8(x_9, 3);
x_17 = lean_ctor_get_uint8(x_9, 4);
x_18 = lean_ctor_get_uint8(x_9, 5);
x_19 = lean_ctor_get_uint8(x_9, 6);
x_20 = lean_ctor_get_uint8(x_9, 8);
x_21 = lean_ctor_get_uint8(x_9, 9);
x_22 = lean_ctor_get_uint8(x_9, 10);
x_23 = lean_ctor_get_uint8(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_26, 0, x_13);
lean_ctor_set_uint8(x_26, 1, x_14);
lean_ctor_set_uint8(x_26, 2, x_15);
lean_ctor_set_uint8(x_26, 3, x_16);
lean_ctor_set_uint8(x_26, 4, x_17);
lean_ctor_set_uint8(x_26, 5, x_18);
lean_ctor_set_uint8(x_26, 6, x_19);
lean_ctor_set_uint8(x_26, 7, x_25);
lean_ctor_set_uint8(x_26, 8, x_20);
lean_ctor_set_uint8(x_26, 9, x_21);
lean_ctor_set_uint8(x_26, 10, x_22);
lean_ctor_set_uint8(x_26, 11, x_23);
lean_ctor_set_uint8(x_26, 12, x_24);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_33 = lean_ctor_get_uint8(x_28, 0);
x_34 = lean_ctor_get_uint8(x_28, 1);
x_35 = lean_ctor_get_uint8(x_28, 2);
x_36 = lean_ctor_get_uint8(x_28, 3);
x_37 = lean_ctor_get_uint8(x_28, 4);
x_38 = lean_ctor_get_uint8(x_28, 5);
x_39 = lean_ctor_get_uint8(x_28, 6);
x_40 = lean_ctor_get_uint8(x_28, 8);
x_41 = lean_ctor_get_uint8(x_28, 9);
x_42 = lean_ctor_get_uint8(x_28, 10);
x_43 = lean_ctor_get_uint8(x_28, 11);
x_44 = lean_ctor_get_uint8(x_28, 12);
if (lean_is_exclusive(x_28)) {
 x_45 = x_28;
} else {
 lean_dec_ref(x_28);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 13);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_33);
lean_ctor_set_uint8(x_47, 1, x_34);
lean_ctor_set_uint8(x_47, 2, x_35);
lean_ctor_set_uint8(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, 4, x_37);
lean_ctor_set_uint8(x_47, 5, x_38);
lean_ctor_set_uint8(x_47, 6, x_39);
lean_ctor_set_uint8(x_47, 7, x_46);
lean_ctor_set_uint8(x_47, 8, x_40);
lean_ctor_set_uint8(x_47, 9, x_41);
lean_ctor_set_uint8(x_47, 10, x_42);
lean_ctor_set_uint8(x_47, 11, x_43);
lean_ctor_set_uint8(x_47, 12, x_44);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_31);
lean_ctor_set(x_48, 4, x_32);
x_49 = lean_apply_7(x_2, lean_box(0), x_1, x_48, x_4, x_5, x_6, x_7);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withTrackingZeta___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = 0;
lean_ctor_set_uint8(x_9, 9, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get_uint8(x_9, 0);
x_14 = lean_ctor_get_uint8(x_9, 1);
x_15 = lean_ctor_get_uint8(x_9, 2);
x_16 = lean_ctor_get_uint8(x_9, 3);
x_17 = lean_ctor_get_uint8(x_9, 4);
x_18 = lean_ctor_get_uint8(x_9, 5);
x_19 = lean_ctor_get_uint8(x_9, 6);
x_20 = lean_ctor_get_uint8(x_9, 7);
x_21 = lean_ctor_get_uint8(x_9, 8);
x_22 = lean_ctor_get_uint8(x_9, 10);
x_23 = lean_ctor_get_uint8(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_26, 0, x_13);
lean_ctor_set_uint8(x_26, 1, x_14);
lean_ctor_set_uint8(x_26, 2, x_15);
lean_ctor_set_uint8(x_26, 3, x_16);
lean_ctor_set_uint8(x_26, 4, x_17);
lean_ctor_set_uint8(x_26, 5, x_18);
lean_ctor_set_uint8(x_26, 6, x_19);
lean_ctor_set_uint8(x_26, 7, x_20);
lean_ctor_set_uint8(x_26, 8, x_21);
lean_ctor_set_uint8(x_26, 9, x_25);
lean_ctor_set_uint8(x_26, 10, x_22);
lean_ctor_set_uint8(x_26, 11, x_23);
lean_ctor_set_uint8(x_26, 12, x_24);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_33 = lean_ctor_get_uint8(x_28, 0);
x_34 = lean_ctor_get_uint8(x_28, 1);
x_35 = lean_ctor_get_uint8(x_28, 2);
x_36 = lean_ctor_get_uint8(x_28, 3);
x_37 = lean_ctor_get_uint8(x_28, 4);
x_38 = lean_ctor_get_uint8(x_28, 5);
x_39 = lean_ctor_get_uint8(x_28, 6);
x_40 = lean_ctor_get_uint8(x_28, 7);
x_41 = lean_ctor_get_uint8(x_28, 8);
x_42 = lean_ctor_get_uint8(x_28, 10);
x_43 = lean_ctor_get_uint8(x_28, 11);
x_44 = lean_ctor_get_uint8(x_28, 12);
if (lean_is_exclusive(x_28)) {
 x_45 = x_28;
} else {
 lean_dec_ref(x_28);
 x_45 = lean_box(0);
}
x_46 = 0;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 13);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_33);
lean_ctor_set_uint8(x_47, 1, x_34);
lean_ctor_set_uint8(x_47, 2, x_35);
lean_ctor_set_uint8(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, 4, x_37);
lean_ctor_set_uint8(x_47, 5, x_38);
lean_ctor_set_uint8(x_47, 6, x_39);
lean_ctor_set_uint8(x_47, 7, x_40);
lean_ctor_set_uint8(x_47, 8, x_41);
lean_ctor_set_uint8(x_47, 9, x_46);
lean_ctor_set_uint8(x_47, 10, x_42);
lean_ctor_set_uint8(x_47, 11, x_43);
lean_ctor_set_uint8(x_47, 12, x_44);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_31);
lean_ctor_set(x_48, 4, x_32);
x_49 = lean_apply_7(x_2, lean_box(0), x_1, x_48, x_4, x_5, x_6, x_7);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withoutProofIrrelevance___rarg___lambda__1), 7, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withoutProofIrrelevance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withoutProofIrrelevance___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get_uint8(x_10, 0);
x_22 = lean_ctor_get_uint8(x_10, 1);
x_23 = lean_ctor_get_uint8(x_10, 2);
x_24 = lean_ctor_get_uint8(x_10, 3);
x_25 = lean_ctor_get_uint8(x_10, 4);
x_26 = lean_ctor_get_uint8(x_10, 6);
x_27 = lean_ctor_get_uint8(x_10, 7);
x_28 = lean_ctor_get_uint8(x_10, 8);
x_29 = lean_ctor_get_uint8(x_10, 9);
x_30 = lean_ctor_get_uint8(x_10, 10);
x_31 = lean_ctor_get_uint8(x_10, 11);
x_32 = lean_ctor_get_uint8(x_10, 12);
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_33, 0, x_21);
lean_ctor_set_uint8(x_33, 1, x_22);
lean_ctor_set_uint8(x_33, 2, x_23);
lean_ctor_set_uint8(x_33, 3, x_24);
lean_ctor_set_uint8(x_33, 4, x_25);
lean_ctor_set_uint8(x_33, 5, x_1);
lean_ctor_set_uint8(x_33, 6, x_26);
lean_ctor_set_uint8(x_33, 7, x_27);
lean_ctor_set_uint8(x_33, 8, x_28);
lean_ctor_set_uint8(x_33, 9, x_29);
lean_ctor_set_uint8(x_33, 10, x_30);
lean_ctor_set_uint8(x_33, 11, x_31);
lean_ctor_set_uint8(x_33, 12, x_32);
lean_ctor_set(x_4, 0, x_33);
x_34 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_48 = lean_ctor_get_uint8(x_43, 0);
x_49 = lean_ctor_get_uint8(x_43, 1);
x_50 = lean_ctor_get_uint8(x_43, 2);
x_51 = lean_ctor_get_uint8(x_43, 3);
x_52 = lean_ctor_get_uint8(x_43, 4);
x_53 = lean_ctor_get_uint8(x_43, 6);
x_54 = lean_ctor_get_uint8(x_43, 7);
x_55 = lean_ctor_get_uint8(x_43, 8);
x_56 = lean_ctor_get_uint8(x_43, 9);
x_57 = lean_ctor_get_uint8(x_43, 10);
x_58 = lean_ctor_get_uint8(x_43, 11);
x_59 = lean_ctor_get_uint8(x_43, 12);
if (lean_is_exclusive(x_43)) {
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 0, 13);
} else {
 x_61 = x_60;
}
lean_ctor_set_uint8(x_61, 0, x_48);
lean_ctor_set_uint8(x_61, 1, x_49);
lean_ctor_set_uint8(x_61, 2, x_50);
lean_ctor_set_uint8(x_61, 3, x_51);
lean_ctor_set_uint8(x_61, 4, x_52);
lean_ctor_set_uint8(x_61, 5, x_1);
lean_ctor_set_uint8(x_61, 6, x_53);
lean_ctor_set_uint8(x_61, 7, x_54);
lean_ctor_set_uint8(x_61, 8, x_55);
lean_ctor_set_uint8(x_61, 9, x_56);
lean_ctor_set_uint8(x_61, 10, x_57);
lean_ctor_set_uint8(x_61, 11, x_58);
lean_ctor_set_uint8(x_61, 12, x_59);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_62, 3, x_46);
lean_ctor_set(x_62, 4, x_47);
x_63 = lean_apply_7(x_3, lean_box(0), x_2, x_62, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withTransparency___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_withTransparency___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_withTransparency___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
x_29 = lean_ctor_get_uint8(x_9, 9);
x_30 = lean_ctor_get_uint8(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, 11);
x_32 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_34, 0, x_21);
lean_ctor_set_uint8(x_34, 1, x_22);
lean_ctor_set_uint8(x_34, 2, x_23);
lean_ctor_set_uint8(x_34, 3, x_24);
lean_ctor_set_uint8(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, 5, x_33);
lean_ctor_set_uint8(x_34, 6, x_26);
lean_ctor_set_uint8(x_34, 7, x_27);
lean_ctor_set_uint8(x_34, 8, x_28);
lean_ctor_set_uint8(x_34, 9, x_29);
lean_ctor_set_uint8(x_34, 10, x_30);
lean_ctor_set_uint8(x_34, 11, x_31);
lean_ctor_set_uint8(x_34, 12, x_32);
lean_ctor_set(x_3, 0, x_34);
x_35 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_42 = x_35;
} else {
 lean_dec_ref(x_35);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_49 = lean_ctor_get_uint8(x_44, 0);
x_50 = lean_ctor_get_uint8(x_44, 1);
x_51 = lean_ctor_get_uint8(x_44, 2);
x_52 = lean_ctor_get_uint8(x_44, 3);
x_53 = lean_ctor_get_uint8(x_44, 4);
x_54 = lean_ctor_get_uint8(x_44, 6);
x_55 = lean_ctor_get_uint8(x_44, 7);
x_56 = lean_ctor_get_uint8(x_44, 8);
x_57 = lean_ctor_get_uint8(x_44, 9);
x_58 = lean_ctor_get_uint8(x_44, 10);
x_59 = lean_ctor_get_uint8(x_44, 11);
x_60 = lean_ctor_get_uint8(x_44, 12);
if (lean_is_exclusive(x_44)) {
 x_61 = x_44;
} else {
 lean_dec_ref(x_44);
 x_61 = lean_box(0);
}
x_62 = 1;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 0, 13);
} else {
 x_63 = x_61;
}
lean_ctor_set_uint8(x_63, 0, x_49);
lean_ctor_set_uint8(x_63, 1, x_50);
lean_ctor_set_uint8(x_63, 2, x_51);
lean_ctor_set_uint8(x_63, 3, x_52);
lean_ctor_set_uint8(x_63, 4, x_53);
lean_ctor_set_uint8(x_63, 5, x_62);
lean_ctor_set_uint8(x_63, 6, x_54);
lean_ctor_set_uint8(x_63, 7, x_55);
lean_ctor_set_uint8(x_63, 8, x_56);
lean_ctor_set_uint8(x_63, 9, x_57);
lean_ctor_set_uint8(x_63, 10, x_58);
lean_ctor_set_uint8(x_63, 11, x_59);
lean_ctor_set_uint8(x_63, 12, x_60);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_46);
lean_ctor_set(x_64, 3, x_47);
lean_ctor_set(x_64, 4, x_48);
x_65 = lean_apply_7(x_2, lean_box(0), x_1, x_64, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withDefault___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
x_29 = lean_ctor_get_uint8(x_9, 9);
x_30 = lean_ctor_get_uint8(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, 11);
x_32 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_33 = 2;
x_34 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_34, 0, x_21);
lean_ctor_set_uint8(x_34, 1, x_22);
lean_ctor_set_uint8(x_34, 2, x_23);
lean_ctor_set_uint8(x_34, 3, x_24);
lean_ctor_set_uint8(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, 5, x_33);
lean_ctor_set_uint8(x_34, 6, x_26);
lean_ctor_set_uint8(x_34, 7, x_27);
lean_ctor_set_uint8(x_34, 8, x_28);
lean_ctor_set_uint8(x_34, 9, x_29);
lean_ctor_set_uint8(x_34, 10, x_30);
lean_ctor_set_uint8(x_34, 11, x_31);
lean_ctor_set_uint8(x_34, 12, x_32);
lean_ctor_set(x_3, 0, x_34);
x_35 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_42 = x_35;
} else {
 lean_dec_ref(x_35);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_49 = lean_ctor_get_uint8(x_44, 0);
x_50 = lean_ctor_get_uint8(x_44, 1);
x_51 = lean_ctor_get_uint8(x_44, 2);
x_52 = lean_ctor_get_uint8(x_44, 3);
x_53 = lean_ctor_get_uint8(x_44, 4);
x_54 = lean_ctor_get_uint8(x_44, 6);
x_55 = lean_ctor_get_uint8(x_44, 7);
x_56 = lean_ctor_get_uint8(x_44, 8);
x_57 = lean_ctor_get_uint8(x_44, 9);
x_58 = lean_ctor_get_uint8(x_44, 10);
x_59 = lean_ctor_get_uint8(x_44, 11);
x_60 = lean_ctor_get_uint8(x_44, 12);
if (lean_is_exclusive(x_44)) {
 x_61 = x_44;
} else {
 lean_dec_ref(x_44);
 x_61 = lean_box(0);
}
x_62 = 2;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 0, 13);
} else {
 x_63 = x_61;
}
lean_ctor_set_uint8(x_63, 0, x_49);
lean_ctor_set_uint8(x_63, 1, x_50);
lean_ctor_set_uint8(x_63, 2, x_51);
lean_ctor_set_uint8(x_63, 3, x_52);
lean_ctor_set_uint8(x_63, 4, x_53);
lean_ctor_set_uint8(x_63, 5, x_62);
lean_ctor_set_uint8(x_63, 6, x_54);
lean_ctor_set_uint8(x_63, 7, x_55);
lean_ctor_set_uint8(x_63, 8, x_56);
lean_ctor_set_uint8(x_63, 9, x_57);
lean_ctor_set_uint8(x_63, 10, x_58);
lean_ctor_set_uint8(x_63, 11, x_59);
lean_ctor_set_uint8(x_63, 12, x_60);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_46);
lean_ctor_set(x_64, 3, x_47);
lean_ctor_set(x_64, 4, x_48);
x_65 = lean_apply_7(x_2, lean_box(0), x_1, x_64, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withReducible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withReducible___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
x_29 = lean_ctor_get_uint8(x_9, 9);
x_30 = lean_ctor_get_uint8(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, 11);
x_32 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_34, 0, x_21);
lean_ctor_set_uint8(x_34, 1, x_22);
lean_ctor_set_uint8(x_34, 2, x_23);
lean_ctor_set_uint8(x_34, 3, x_24);
lean_ctor_set_uint8(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, 5, x_33);
lean_ctor_set_uint8(x_34, 6, x_26);
lean_ctor_set_uint8(x_34, 7, x_27);
lean_ctor_set_uint8(x_34, 8, x_28);
lean_ctor_set_uint8(x_34, 9, x_29);
lean_ctor_set_uint8(x_34, 10, x_30);
lean_ctor_set_uint8(x_34, 11, x_31);
lean_ctor_set_uint8(x_34, 12, x_32);
lean_ctor_set(x_3, 0, x_34);
x_35 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_42 = x_35;
} else {
 lean_dec_ref(x_35);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_49 = lean_ctor_get_uint8(x_44, 0);
x_50 = lean_ctor_get_uint8(x_44, 1);
x_51 = lean_ctor_get_uint8(x_44, 2);
x_52 = lean_ctor_get_uint8(x_44, 3);
x_53 = lean_ctor_get_uint8(x_44, 4);
x_54 = lean_ctor_get_uint8(x_44, 6);
x_55 = lean_ctor_get_uint8(x_44, 7);
x_56 = lean_ctor_get_uint8(x_44, 8);
x_57 = lean_ctor_get_uint8(x_44, 9);
x_58 = lean_ctor_get_uint8(x_44, 10);
x_59 = lean_ctor_get_uint8(x_44, 11);
x_60 = lean_ctor_get_uint8(x_44, 12);
if (lean_is_exclusive(x_44)) {
 x_61 = x_44;
} else {
 lean_dec_ref(x_44);
 x_61 = lean_box(0);
}
x_62 = 3;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 0, 13);
} else {
 x_63 = x_61;
}
lean_ctor_set_uint8(x_63, 0, x_49);
lean_ctor_set_uint8(x_63, 1, x_50);
lean_ctor_set_uint8(x_63, 2, x_51);
lean_ctor_set_uint8(x_63, 3, x_52);
lean_ctor_set_uint8(x_63, 4, x_53);
lean_ctor_set_uint8(x_63, 5, x_62);
lean_ctor_set_uint8(x_63, 6, x_54);
lean_ctor_set_uint8(x_63, 7, x_55);
lean_ctor_set_uint8(x_63, 8, x_56);
lean_ctor_set_uint8(x_63, 9, x_57);
lean_ctor_set_uint8(x_63, 10, x_58);
lean_ctor_set_uint8(x_63, 11, x_59);
lean_ctor_set_uint8(x_63, 12, x_60);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_46);
lean_ctor_set(x_64, 3, x_47);
lean_ctor_set(x_64, 4, x_48);
x_65 = lean_apply_7(x_2, lean_box(0), x_1, x_64, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withReducibleAndInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withReducibleAndInstances___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_16 = lean_ctor_get_uint8(x_10, 0);
x_17 = lean_ctor_get_uint8(x_10, 1);
x_18 = lean_ctor_get_uint8(x_10, 2);
x_19 = lean_ctor_get_uint8(x_10, 3);
x_20 = lean_ctor_get_uint8(x_10, 4);
x_21 = lean_ctor_get_uint8(x_10, 5);
x_22 = lean_ctor_get_uint8(x_10, 6);
x_23 = lean_ctor_get_uint8(x_10, 7);
x_24 = lean_ctor_get_uint8(x_10, 8);
x_25 = lean_ctor_get_uint8(x_10, 9);
x_26 = lean_ctor_get_uint8(x_10, 10);
x_27 = lean_ctor_get_uint8(x_10, 11);
x_28 = lean_ctor_get_uint8(x_10, 12);
lean_dec(x_10);
x_29 = l_Lean_Meta_TransparencyMode_lt(x_21, x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_30, 0, x_16);
lean_ctor_set_uint8(x_30, 1, x_17);
lean_ctor_set_uint8(x_30, 2, x_18);
lean_ctor_set_uint8(x_30, 3, x_19);
lean_ctor_set_uint8(x_30, 4, x_20);
lean_ctor_set_uint8(x_30, 5, x_21);
lean_ctor_set_uint8(x_30, 6, x_22);
lean_ctor_set_uint8(x_30, 7, x_23);
lean_ctor_set_uint8(x_30, 8, x_24);
lean_ctor_set_uint8(x_30, 9, x_25);
lean_ctor_set_uint8(x_30, 10, x_26);
lean_ctor_set_uint8(x_30, 11, x_27);
lean_ctor_set_uint8(x_30, 12, x_28);
lean_ctor_set(x_4, 0, x_30);
x_31 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_32, 0, x_16);
lean_ctor_set_uint8(x_32, 1, x_17);
lean_ctor_set_uint8(x_32, 2, x_18);
lean_ctor_set_uint8(x_32, 3, x_19);
lean_ctor_set_uint8(x_32, 4, x_20);
lean_ctor_set_uint8(x_32, 5, x_1);
lean_ctor_set_uint8(x_32, 6, x_22);
lean_ctor_set_uint8(x_32, 7, x_23);
lean_ctor_set_uint8(x_32, 8, x_24);
lean_ctor_set_uint8(x_32, 9, x_25);
lean_ctor_set_uint8(x_32, 10, x_26);
lean_ctor_set_uint8(x_32, 11, x_27);
lean_ctor_set_uint8(x_32, 12, x_28);
lean_ctor_set(x_4, 0, x_32);
x_33 = lean_apply_7(x_3, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get(x_4, 2);
x_37 = lean_ctor_get(x_4, 3);
x_38 = lean_ctor_get(x_4, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_39 = lean_ctor_get_uint8(x_34, 0);
x_40 = lean_ctor_get_uint8(x_34, 1);
x_41 = lean_ctor_get_uint8(x_34, 2);
x_42 = lean_ctor_get_uint8(x_34, 3);
x_43 = lean_ctor_get_uint8(x_34, 4);
x_44 = lean_ctor_get_uint8(x_34, 5);
x_45 = lean_ctor_get_uint8(x_34, 6);
x_46 = lean_ctor_get_uint8(x_34, 7);
x_47 = lean_ctor_get_uint8(x_34, 8);
x_48 = lean_ctor_get_uint8(x_34, 9);
x_49 = lean_ctor_get_uint8(x_34, 10);
x_50 = lean_ctor_get_uint8(x_34, 11);
x_51 = lean_ctor_get_uint8(x_34, 12);
if (lean_is_exclusive(x_34)) {
 x_52 = x_34;
} else {
 lean_dec_ref(x_34);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Meta_TransparencyMode_lt(x_44, x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 0, 13);
} else {
 x_54 = x_52;
}
lean_ctor_set_uint8(x_54, 0, x_39);
lean_ctor_set_uint8(x_54, 1, x_40);
lean_ctor_set_uint8(x_54, 2, x_41);
lean_ctor_set_uint8(x_54, 3, x_42);
lean_ctor_set_uint8(x_54, 4, x_43);
lean_ctor_set_uint8(x_54, 5, x_44);
lean_ctor_set_uint8(x_54, 6, x_45);
lean_ctor_set_uint8(x_54, 7, x_46);
lean_ctor_set_uint8(x_54, 8, x_47);
lean_ctor_set_uint8(x_54, 9, x_48);
lean_ctor_set_uint8(x_54, 10, x_49);
lean_ctor_set_uint8(x_54, 11, x_50);
lean_ctor_set_uint8(x_54, 12, x_51);
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_36);
lean_ctor_set(x_55, 3, x_37);
lean_ctor_set(x_55, 4, x_38);
x_56 = lean_apply_7(x_3, lean_box(0), x_2, x_55, x_5, x_6, x_7, x_8);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 0, 13);
} else {
 x_57 = x_52;
}
lean_ctor_set_uint8(x_57, 0, x_39);
lean_ctor_set_uint8(x_57, 1, x_40);
lean_ctor_set_uint8(x_57, 2, x_41);
lean_ctor_set_uint8(x_57, 3, x_42);
lean_ctor_set_uint8(x_57, 4, x_43);
lean_ctor_set_uint8(x_57, 5, x_1);
lean_ctor_set_uint8(x_57, 6, x_45);
lean_ctor_set_uint8(x_57, 7, x_46);
lean_ctor_set_uint8(x_57, 8, x_47);
lean_ctor_set_uint8(x_57, 9, x_48);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set(x_58, 4, x_38);
x_59 = lean_apply_7(x_3, lean_box(0), x_2, x_58, x_5, x_6, x_7, x_8);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withAtLeastTransparency___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_withAtLeastTransparency___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAtLeastTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_withAtLeastTransparency___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_ctor_set_uint8(x_9, 10, x_11);
x_12 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get_uint8(x_9, 0);
x_14 = lean_ctor_get_uint8(x_9, 1);
x_15 = lean_ctor_get_uint8(x_9, 2);
x_16 = lean_ctor_get_uint8(x_9, 3);
x_17 = lean_ctor_get_uint8(x_9, 4);
x_18 = lean_ctor_get_uint8(x_9, 5);
x_19 = lean_ctor_get_uint8(x_9, 6);
x_20 = lean_ctor_get_uint8(x_9, 7);
x_21 = lean_ctor_get_uint8(x_9, 8);
x_22 = lean_ctor_get_uint8(x_9, 9);
x_23 = lean_ctor_get_uint8(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_26, 0, x_13);
lean_ctor_set_uint8(x_26, 1, x_14);
lean_ctor_set_uint8(x_26, 2, x_15);
lean_ctor_set_uint8(x_26, 3, x_16);
lean_ctor_set_uint8(x_26, 4, x_17);
lean_ctor_set_uint8(x_26, 5, x_18);
lean_ctor_set_uint8(x_26, 6, x_19);
lean_ctor_set_uint8(x_26, 7, x_20);
lean_ctor_set_uint8(x_26, 8, x_21);
lean_ctor_set_uint8(x_26, 9, x_22);
lean_ctor_set_uint8(x_26, 10, x_25);
lean_ctor_set_uint8(x_26, 11, x_23);
lean_ctor_set_uint8(x_26, 12, x_24);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_33 = lean_ctor_get_uint8(x_28, 0);
x_34 = lean_ctor_get_uint8(x_28, 1);
x_35 = lean_ctor_get_uint8(x_28, 2);
x_36 = lean_ctor_get_uint8(x_28, 3);
x_37 = lean_ctor_get_uint8(x_28, 4);
x_38 = lean_ctor_get_uint8(x_28, 5);
x_39 = lean_ctor_get_uint8(x_28, 6);
x_40 = lean_ctor_get_uint8(x_28, 7);
x_41 = lean_ctor_get_uint8(x_28, 8);
x_42 = lean_ctor_get_uint8(x_28, 9);
x_43 = lean_ctor_get_uint8(x_28, 11);
x_44 = lean_ctor_get_uint8(x_28, 12);
if (lean_is_exclusive(x_28)) {
 x_45 = x_28;
} else {
 lean_dec_ref(x_28);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 0, 13);
} else {
 x_47 = x_45;
}
lean_ctor_set_uint8(x_47, 0, x_33);
lean_ctor_set_uint8(x_47, 1, x_34);
lean_ctor_set_uint8(x_47, 2, x_35);
lean_ctor_set_uint8(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, 4, x_37);
lean_ctor_set_uint8(x_47, 5, x_38);
lean_ctor_set_uint8(x_47, 6, x_39);
lean_ctor_set_uint8(x_47, 7, x_40);
lean_ctor_set_uint8(x_47, 8, x_41);
lean_ctor_set_uint8(x_47, 9, x_42);
lean_ctor_set_uint8(x_47, 10, x_46);
lean_ctor_set_uint8(x_47, 11, x_43);
lean_ctor_set_uint8(x_47, 12, x_44);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_31);
lean_ctor_set(x_48, 4, x_32);
x_49 = lean_apply_7(x_2, lean_box(0), x_1, x_48, x_4, x_5, x_6, x_7);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_withAssignableSyntheticOpaque___rarg___lambda__1), 7, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withAssignableSyntheticOpaque(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withAssignableSyntheticOpaque___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_savingCacheImpl___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_savingCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_savingCache___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getTheoremInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getTheoremInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
x_8 = l_Lean_mkConst(x_1, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2(x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_15)) {
case 1:
{
lean_object* x_16; 
lean_free_object(x_12);
lean_free_object(x_7);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(x_15, x_2, x_3, x_4, x_5, x_10);
return x_16;
}
case 2:
{
lean_object* x_17; 
lean_free_object(x_12);
lean_free_object(x_7);
x_17 = l_Lean_Meta_getTheoremInfo(x_15, x_2, x_3, x_4, x_5, x_10);
return x_17;
}
default: 
{
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
switch (lean_obj_tag(x_18)) {
case 1:
{
lean_object* x_19; 
lean_free_object(x_7);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(x_18, x_2, x_3, x_4, x_5, x_10);
return x_19;
}
case 2:
{
lean_object* x_20; 
lean_free_object(x_7);
x_20 = l_Lean_Meta_getTheoremInfo(x_18, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
default: 
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
}
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
lean_object* x_26; 
x_26 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
switch (lean_obj_tag(x_27)) {
case 1:
{
lean_object* x_29; 
lean_dec(x_28);
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp(x_27, x_2, x_3, x_4, x_5, x_23);
return x_29;
}
case 2:
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = l_Lean_Meta_getTheoremInfo(x_27, x_2, x_3, x_4, x_5, x_23);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuickConst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 3);
x_31 = lean_ctor_get(x_16, 4);
x_32 = lean_ctor_get(x_16, 5);
x_33 = lean_ctor_get(x_16, 6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_34 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
x_35 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_15, 1, x_35);
x_36 = lean_st_ref_set(x_1, x_15, x_17);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 2);
x_42 = lean_ctor_get(x_15, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_16, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_16, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_16, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Meta_Cache_synthInstance___default___closed__1;
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set(x_52, 3, x_42);
x_53 = lean_st_ref_set(x_1, x_52, x_17);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_saveAndResetSynthInstanceCache(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_1);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set(x_10, 1, x_30);
x_31 = lean_st_ref_set(x_3, x_10, x_12);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 2);
x_38 = lean_ctor_get(x_10, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 6);
lean_inc(x_44);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_45 = x_11;
} else {
 lean_dec_ref(x_11);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 7, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_1);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_42);
lean_ctor_set(x_46, 5, x_43);
lean_ctor_set(x_46, 6, x_44);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 3, x_38);
x_48 = lean_st_ref_set(x_3, x_47, x_12);
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
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_restoreSynthInstanceCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_resettingSynthInstanceCacheImpl___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCache___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_resettingSynthInstanceCacheWhen___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 4);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_array_push(x_20, x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_apply_5(x_3, x_25, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_restoreSynthInstanceCache(x_16, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_restoreSynthInstanceCache(x_16, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
return x_9;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__2___rarg(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = lean_whnf(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_isForall(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_apply_7(x_2, x_3, x_1, x_8, x_9, x_10, x_11, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_4, x_5, x_2, x_6, x_3, x_7, x_14, x_8, x_9, x_10, x_11, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_20, x_28, x_9, x_10, x_11, x_12);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
x_30 = lean_array_get_size(x_5);
x_31 = lean_expr_instantiate_rev_range(x_14, x_6, x_30, x_5);
lean_dec(x_30);
lean_dec(x_14);
x_32 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_11, x_12);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = (uint8_t)((x_16 << 24) >> 61);
lean_inc(x_33);
x_36 = lean_local_ctx_mk_local_decl(x_4, x_33, x_13, x_31, x_35);
x_37 = l_Lean_mkFVar(x_33);
x_38 = lean_array_push(x_5, x_37);
x_4 = x_36;
x_5 = x_38;
x_7 = x_15;
x_12 = x_34;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_array_get_size(x_5);
x_41 = lean_expr_instantiate_rev_range(x_7, x_6, x_40, x_5);
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_40);
lean_dec(x_2);
lean_inc(x_5);
x_42 = lean_apply_2(x_3, x_5, x_41);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 1);
lean_dec(x_44);
lean_ctor_set(x_8, 1, x_4);
x_45 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_42, x_8, x_9, x_10, x_11, x_12);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 2);
x_48 = lean_ctor_get(x_8, 3);
x_49 = lean_ctor_get(x_8, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_4);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_42, x_50, x_9, x_10, x_11, x_12);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = l___private_Lean_Meta_Basic_0__Lean_Meta_fvarsSizeLtMaxFVars(x_5, x_2);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_40);
lean_dec(x_2);
lean_inc(x_5);
x_53 = lean_apply_2(x_3, x_5, x_41);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_8, 1);
lean_dec(x_55);
lean_ctor_set(x_8, 1, x_4);
x_56 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_53, x_8, x_9, x_10, x_11, x_12);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 2);
x_59 = lean_ctor_get(x_8, 3);
x_60 = lean_ctor_get(x_8, 4);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_4);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_60);
x_62 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_53, x_61, x_9, x_10, x_11, x_12);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_5);
x_64 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed), 12, 7);
lean_closure_set(x_64, 0, x_41);
lean_closure_set(x_64, 1, x_3);
lean_closure_set(x_64, 2, x_5);
lean_closure_set(x_64, 3, x_63);
lean_closure_set(x_64, 4, x_2);
lean_closure_set(x_64, 5, x_4);
lean_closure_set(x_64, 6, x_40);
x_65 = !lean_is_exclusive(x_8);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_8, 1);
lean_dec(x_66);
lean_ctor_set(x_8, 1, x_4);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_64, x_8, x_9, x_10, x_11, x_12);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 2);
x_70 = lean_ctor_get(x_8, 3);
x_71 = lean_ctor_get(x_8, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_4);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_5, x_6, x_64, x_72, x_9, x_10, x_11, x_12);
return x_73;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_12);
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
x_44 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_39);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get_uint8(x_9, 0);
x_23 = lean_ctor_get_uint8(x_9, 1);
x_24 = lean_ctor_get_uint8(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, 4);
x_27 = lean_ctor_get_uint8(x_9, 6);
x_28 = lean_ctor_get_uint8(x_9, 7);
x_29 = lean_ctor_get_uint8(x_9, 8);
x_30 = lean_ctor_get_uint8(x_9, 9);
x_31 = lean_ctor_get_uint8(x_9, 10);
x_32 = lean_ctor_get_uint8(x_9, 11);
x_33 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_34 = 2;
x_35 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_35, 0, x_22);
lean_ctor_set_uint8(x_35, 1, x_23);
lean_ctor_set_uint8(x_35, 2, x_24);
lean_ctor_set_uint8(x_35, 3, x_25);
lean_ctor_set_uint8(x_35, 4, x_26);
lean_ctor_set_uint8(x_35, 5, x_34);
lean_ctor_set_uint8(x_35, 6, x_27);
lean_ctor_set_uint8(x_35, 7, x_28);
lean_ctor_set_uint8(x_35, 8, x_29);
lean_ctor_set_uint8(x_35, 9, x_30);
lean_ctor_set_uint8(x_35, 10, x_31);
lean_ctor_set_uint8(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, 12, x_33);
lean_ctor_set(x_2, 0, x_35);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_7, x_36, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
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
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 3);
x_50 = lean_ctor_get(x_2, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_51 = lean_ctor_get_uint8(x_46, 0);
x_52 = lean_ctor_get_uint8(x_46, 1);
x_53 = lean_ctor_get_uint8(x_46, 2);
x_54 = lean_ctor_get_uint8(x_46, 3);
x_55 = lean_ctor_get_uint8(x_46, 4);
x_56 = lean_ctor_get_uint8(x_46, 6);
x_57 = lean_ctor_get_uint8(x_46, 7);
x_58 = lean_ctor_get_uint8(x_46, 8);
x_59 = lean_ctor_get_uint8(x_46, 9);
x_60 = lean_ctor_get_uint8(x_46, 10);
x_61 = lean_ctor_get_uint8(x_46, 11);
x_62 = lean_ctor_get_uint8(x_46, 12);
if (lean_is_exclusive(x_46)) {
 x_63 = x_46;
} else {
 lean_dec_ref(x_46);
 x_63 = lean_box(0);
}
x_64 = 2;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 0, 13);
} else {
 x_65 = x_63;
}
lean_ctor_set_uint8(x_65, 0, x_51);
lean_ctor_set_uint8(x_65, 1, x_52);
lean_ctor_set_uint8(x_65, 2, x_53);
lean_ctor_set_uint8(x_65, 3, x_54);
lean_ctor_set_uint8(x_65, 4, x_55);
lean_ctor_set_uint8(x_65, 5, x_64);
lean_ctor_set_uint8(x_65, 6, x_56);
lean_ctor_set_uint8(x_65, 7, x_57);
lean_ctor_set_uint8(x_65, 8, x_58);
lean_ctor_set_uint8(x_65, 9, x_59);
lean_ctor_set_uint8(x_65, 10, x_60);
lean_ctor_set_uint8(x_65, 11, x_61);
lean_ctor_set_uint8(x_65, 12, x_62);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_47);
lean_ctor_set(x_66, 2, x_48);
lean_ctor_set(x_66, 3, x_49);
lean_ctor_set(x_66, 4, x_50);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___closed__1;
x_68 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_7, x_67, x_66, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = lean_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
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
x_13 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
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
x_24 = lean_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
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
x_28 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
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
x_36 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_37 = lean_apply_7(x_3, x_36, x_1, x_4, x_5, x_6, x_7, x_8);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_1, x_2, x_4, x_10, x_11, x_12, x_3, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_isClass_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewLocalInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_9, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_forallBoundedTelescopeImp___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_18 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_10, x_11);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 2);
x_34 = lean_ctor_get(x_7, 3);
x_35 = lean_ctor_get(x_7, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_3);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_35);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_28, x_36, x_8, x_9, x_10, x_11);
return x_37;
}
}
}
else
{
switch (lean_obj_tag(x_6)) {
case 6:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_42 = lean_array_get_size(x_4);
x_43 = lean_expr_instantiate_rev_range(x_39, x_5, x_42, x_4);
lean_dec(x_42);
lean_dec(x_39);
x_44 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_10, x_11);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = (uint8_t)((x_41 << 24) >> 61);
lean_inc(x_45);
x_48 = lean_local_ctx_mk_local_decl(x_3, x_45, x_38, x_43, x_47);
x_49 = l_Lean_mkFVar(x_45);
x_50 = lean_array_push(x_4, x_49);
x_3 = x_48;
x_4 = x_50;
x_6 = x_40;
x_11 = x_46;
goto _start;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_52 = lean_ctor_get(x_6, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_6, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_6, 3);
lean_inc(x_55);
lean_dec(x_6);
x_56 = lean_array_get_size(x_4);
x_57 = lean_expr_instantiate_rev_range(x_53, x_5, x_56, x_4);
lean_dec(x_53);
x_58 = lean_expr_instantiate_rev_range(x_54, x_5, x_56, x_4);
lean_dec(x_56);
lean_dec(x_54);
x_59 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_10, x_11);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = 0;
lean_inc(x_60);
x_63 = lean_local_ctx_mk_let_decl(x_3, x_60, x_52, x_57, x_58, x_62);
x_64 = l_Lean_mkFVar(x_60);
x_65 = lean_array_push(x_4, x_64);
x_66 = 1;
x_2 = x_66;
x_3 = x_63;
x_4 = x_65;
x_6 = x_55;
x_11 = x_61;
goto _start;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_array_get_size(x_4);
x_69 = lean_expr_instantiate_rev_range(x_6, x_5, x_68, x_4);
lean_dec(x_68);
lean_dec(x_6);
lean_inc(x_4);
x_70 = lean_apply_2(x_1, x_4, x_69);
x_71 = !lean_is_exclusive(x_7);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_7, 1);
lean_dec(x_72);
lean_ctor_set(x_7, 1, x_3);
x_73 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_70, x_7, x_8, x_9, x_10, x_11);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_7, 0);
x_75 = lean_ctor_get(x_7, 2);
x_76 = lean_ctor_get(x_7, 3);
x_77 = lean_ctor_get(x_7, 4);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_7);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_3);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_76);
lean_ctor_set(x_78, 4, x_77);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg(x_4, x_5, x_70, x_78, x_8, x_9, x_10, x_11);
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp_process___rarg(x_3, x_2, x_9, x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg), 7, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = x_1;
x_11 = lean_box_usize(x_9);
x_12 = l_Lean_Meta_getParamNames___lambda__1___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1___boxed), 8, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_getParamNames___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getParamNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getParamNames___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_get_size(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_14 = x_62;
goto block_61;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_nat_dec_eq(x_63, x_13);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_14 = x_65;
goto block_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_66 = lean_expr_instantiate_rev_range(x_7, x_6, x_13, x_4);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_7);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_5);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_12);
return x_69;
}
}
block_61:
{
lean_dec(x_14);
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_19 = lean_expr_instantiate_rev_range(x_16, x_6, x_13, x_4);
lean_dec(x_13);
lean_dec(x_16);
x_20 = (uint8_t)((x_18 << 24) >> 61);
x_21 = l_Lean_BinderInfo_isInstImplicit(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_8);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_22, x_3, x_15, x_8, x_9, x_10, x_11, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_push(x_4, x_24);
x_27 = lean_box(x_20);
x_28 = lean_array_push(x_5, x_27);
x_4 = x_26;
x_5 = x_28;
x_7 = x_17;
x_12 = x_25;
goto _start;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = 1;
lean_inc(x_8);
x_31 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_22, x_30, x_15, x_8, x_9, x_10, x_11, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_push(x_4, x_32);
x_35 = lean_box(x_20);
x_36 = lean_array_push(x_5, x_35);
x_4 = x_34;
x_5 = x_36;
x_7 = x_17;
x_12 = x_33;
goto _start;
}
}
else
{
lean_object* x_38; 
x_38 = lean_expr_instantiate_rev_range(x_7, x_6, x_13, x_4);
lean_dec(x_6);
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
else
{
lean_object* x_42; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_38);
x_42 = lean_whnf(x_38, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = l_Lean_Expr_isForall(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_38);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_free_object(x_42);
lean_dec(x_38);
x_6 = x_13;
x_7 = x_44;
x_12 = x_45;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = l_Lean_Expr_isForall(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_38);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_dec(x_38);
x_6 = x_13;
x_7 = x_50;
x_12 = x_51;
goto _start;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux_process(x_2, x_3, x_4, x_10, x_10, x_11, x_1, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescope(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_9, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_forallMetaTelescope(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaTelescopeReducing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = 1;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_10, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallMetaBoundedTelescope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_forallMetaBoundedTelescope(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_get_size(x_2);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_12 = x_33;
goto block_32;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_nat_dec_eq(x_34, x_11);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_12 = x_36;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
x_37 = lean_expr_instantiate_rev_range(x_5, x_4, x_11, x_2);
lean_dec(x_11);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
block_32:
{
lean_dec(x_12);
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_16 = lean_expr_instantiate_rev_range(x_13, x_4, x_11, x_2);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_6);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_2, x_21);
x_24 = (uint8_t)((x_15 << 24) >> 61);
x_25 = lean_box(x_24);
x_26 = lean_array_push(x_3, x_25);
x_2 = x_23;
x_3 = x_26;
x_5 = x_14;
x_10 = x_22;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_28 = lean_expr_instantiate_rev_range(x_5, x_4, x_11, x_2);
lean_dec(x_11);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_lambdaMetaTelescope_process(x_2, x_8, x_8, x_9, x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaMetaTelescope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_8, x_9);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
x_22 = lean_ctor_get(x_5, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_11);
x_23 = lean_local_ctx_mk_local_decl(x_19, x_11, x_1, x_3, x_2);
x_24 = l_Lean_mkFVar(x_11);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
x_26 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_24, x_3, x_4, x_25, x_6, x_7, x_8, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_withLocalDecl___rarg___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_withLocalDecl___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_withLocalDecl___rarg(x_1, x_2, lean_box(0), x_4, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_push(x_1, x_7);
x_9 = l_Lean_Meta_withLocalDecls_loop___rarg(x_2, x_3, lean_box(0), x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___rarg___lambda__2), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg(x_2, x_3, lean_box(0), x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_7);
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_1(x_5, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_instInhabitedDepArrow___rarg), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_instInhabitedBinderInfo;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Lean_instInhabitedName;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_get(x_18, x_4, x_8);
lean_dec(x_8);
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
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_7);
x_25 = lean_apply_1(x_23, x_7);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3___boxed), 9, 8);
lean_closure_set(x_26, 0, x_7);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_4);
lean_closure_set(x_26, 4, x_5);
lean_closure_set(x_26, 5, x_6);
lean_closure_set(x_26, 6, x_21);
lean_closure_set(x_26, 7, x_22);
x_27 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_25, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_withLocalDecls_loop___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_Meta_withLocalDecls_loop___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_ParamInfo_backDeps___default___closed__1;
x_8 = l_Lean_Meta_withLocalDecls_loop___rarg(x_1, x_2, lean_box(0), x_5, x_6, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_9);
x_17 = x_16;
x_18 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_11;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = x_25;
x_27 = lean_array_uset(x_8, x_2, x_26);
x_2 = x_11;
x_3 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = x_5;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg(x_8, x_9, x_10);
x_12 = x_11;
x_13 = l_Lean_Meta_withLocalDecls___rarg(x_1, x_2, lean_box(0), x_4, x_12, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclsD___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_withLocalDeclsD___spec__1___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Lean_LocalContext_setBinderInfo(x_4, x_9, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1(x_1, x_16, x_17, x_9);
lean_ctor_set(x_3, 1, x_18);
x_19 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 3);
x_24 = lean_ctor_get(x_3, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_25 = lean_array_get_size(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
x_29 = lean_apply_5(x_2, x_28, x_4, x_5, x_6, x_7);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_25, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
x_32 = lean_apply_5(x_2, x_31, x_4, x_5, x_6, x_7);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1(x_1, x_33, x_34, x_21);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_22);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
x_37 = lean_apply_5(x_2, x_36, x_4, x_5, x_6, x_7);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___rarg___lambda__1___boxed), 8, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewBinderInfos___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_8, x_9);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_24 = 0;
lean_inc(x_2);
lean_inc(x_11);
x_25 = lean_local_ctx_mk_let_decl(x_20, x_11, x_1, x_2, x_3, x_24);
x_26 = l_Lean_mkFVar(x_11);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___rarg(x_26, x_2, x_4, x_27, x_6, x_7, x_8, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_array_get_size(x_11);
lean_inc(x_1);
x_15 = l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(x_10, x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_15);
lean_inc(x_9);
lean_ctor_set(x_3, 1, x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_11, x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_eq(x_19, x_14);
lean_dec(x_14);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_4, x_5, x_6, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = lean_apply_5(x_2, x_24, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_restoreSynthInstanceCache(x_22, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Lean_Meta_restoreSynthInstanceCache(x_22, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
x_40 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_18);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_50 = lean_array_get_size(x_47);
lean_inc(x_1);
x_51 = l_List_foldl___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__1(x_46, x_1);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_51);
lean_inc(x_45);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_52);
x_53 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_47, x_1, x_52, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_eq(x_56, x_50);
lean_dec(x_50);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_4, x_5, x_6, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_48);
lean_ctor_set(x_61, 4, x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = lean_apply_5(x_2, x_61, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_restoreSynthInstanceCache(x_59, x_52, x_4, x_5, x_6, x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_52);
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
x_71 = l_Lean_Meta_restoreSynthInstanceCache(x_59, x_52, x_4, x_5, x_6, x_70);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_52);
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
lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_45);
x_75 = lean_apply_5(x_2, x_52, x_4, x_5, x_6, x_55);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = lean_ctor_get(x_53, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_78 = x_53;
} else {
 lean_dec_ref(x_53);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = l_Lean_MetavarContext_incDepth(x_18);
x_21 = l_Lean_Meta_State_postponed___default___closed__3;
lean_ctor_set(x_15, 3, x_21);
lean_ctor_set(x_15, 0, x_20);
x_22 = lean_st_ref_set(x_3, x_15, x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_3);
x_24 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_5, x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_3, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_30, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
lean_ctor_set(x_30, 3, x_33);
lean_ctor_set(x_30, 0, x_32);
x_37 = lean_st_ref_set(x_3, x_30, x_31);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_25);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_30, 1);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_33);
x_45 = lean_st_ref_set(x_3, x_44, x_31);
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
lean_ctor_set(x_48, 0, x_25);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_st_ref_get(x_5, x_50);
lean_dec(x_5);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_3, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_10, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_10, 3);
lean_inc(x_57);
lean_dec(x_10);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_54, 3);
lean_dec(x_59);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
lean_ctor_set(x_54, 3, x_57);
lean_ctor_set(x_54, 0, x_56);
x_61 = lean_st_ref_set(x_3, x_54, x_55);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_49);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_54, 1);
x_67 = lean_ctor_get(x_54, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_57);
x_69 = lean_st_ref_set(x_3, x_68, x_55);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_49);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get(x_15, 1);
x_75 = lean_ctor_get(x_15, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_15);
x_76 = l_Lean_MetavarContext_incDepth(x_73);
x_77 = l_Lean_Meta_State_postponed___default___closed__3;
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_st_ref_set(x_3, x_78, x_16);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_5);
lean_inc(x_3);
x_81 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_5, x_83);
lean_dec(x_5);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_take(x_3, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_10, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_10, 3);
lean_inc(x_90);
lean_dec(x_10);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 2);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_90);
x_95 = lean_st_ref_set(x_3, x_94, x_88);
lean_dec(x_3);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_81, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_dec(x_81);
x_101 = lean_st_ref_get(x_5, x_100);
lean_dec(x_5);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_st_ref_take(x_3, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_10, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_10, 3);
lean_inc(x_107);
lean_dec(x_10);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 2);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 4, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_107);
x_112 = lean_st_ref_set(x_3, x_111, x_105);
lean_dec(x_3);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_99);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_2, lean_box(0), x_1);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_4, 0);
x_58 = lean_ctor_get(x_4, 3);
x_59 = lean_ctor_get(x_4, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_4);
lean_inc(x_2);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_2);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
if (x_14 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_2);
x_61 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_64 = lean_apply_5(x_3, x_60, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_restoreSynthInstanceCache(x_62, x_60, x_5, x_6, x_7, x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_60);
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
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = l_Lean_Meta_restoreSynthInstanceCache(x_62, x_60, x_5, x_6, x_7, x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_60);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1(x_2, x_10, lean_box(0), x_2, x_10, x_77);
lean_dec(x_10);
lean_dec(x_2);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_5, x_6, x_7, x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_82 = lean_apply_5(x_3, x_60, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_restoreSynthInstanceCache(x_80, x_60, x_5, x_6, x_7, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_60);
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
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_dec(x_82);
x_91 = l_Lean_Meta_restoreSynthInstanceCache(x_80, x_60, x_5, x_6, x_7, x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_60);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; 
x_95 = lean_apply_5(x_3, x_60, x_5, x_6, x_7, x_11);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get_uint8(x_8, 3);
x_21 = lean_ctor_get_uint8(x_8, 4);
x_22 = lean_ctor_get_uint8(x_8, 5);
x_23 = lean_ctor_get_uint8(x_8, 6);
x_24 = lean_ctor_get_uint8(x_8, 7);
x_25 = lean_ctor_get_uint8(x_8, 8);
x_26 = lean_ctor_get_uint8(x_8, 9);
x_27 = lean_ctor_get_uint8(x_8, 10);
x_28 = lean_ctor_get_uint8(x_8, 11);
x_29 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, 3, x_20);
lean_ctor_set_uint8(x_31, 4, x_21);
lean_ctor_set_uint8(x_31, 5, x_22);
lean_ctor_set_uint8(x_31, 6, x_23);
lean_ctor_set_uint8(x_31, 7, x_24);
lean_ctor_set_uint8(x_31, 8, x_25);
lean_ctor_set_uint8(x_31, 9, x_26);
lean_ctor_set_uint8(x_31, 10, x_27);
lean_ctor_set_uint8(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, 12, x_29);
lean_ctor_set(x_2, 0, x_31);
x_32 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_ctor_get(x_2, 3);
x_45 = lean_ctor_get(x_2, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_46 = lean_ctor_get_uint8(x_41, 3);
x_47 = lean_ctor_get_uint8(x_41, 4);
x_48 = lean_ctor_get_uint8(x_41, 5);
x_49 = lean_ctor_get_uint8(x_41, 6);
x_50 = lean_ctor_get_uint8(x_41, 7);
x_51 = lean_ctor_get_uint8(x_41, 8);
x_52 = lean_ctor_get_uint8(x_41, 9);
x_53 = lean_ctor_get_uint8(x_41, 10);
x_54 = lean_ctor_get_uint8(x_41, 11);
x_55 = lean_ctor_get_uint8(x_41, 12);
if (lean_is_exclusive(x_41)) {
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
 x_56 = lean_box(0);
}
x_57 = 1;
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 0, 13);
} else {
 x_58 = x_56;
}
lean_ctor_set_uint8(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, 3, x_46);
lean_ctor_set_uint8(x_58, 4, x_47);
lean_ctor_set_uint8(x_58, 5, x_48);
lean_ctor_set_uint8(x_58, 6, x_49);
lean_ctor_set_uint8(x_58, 7, x_50);
lean_ctor_set_uint8(x_58, 8, x_51);
lean_ctor_set_uint8(x_58, 9, x_52);
lean_ctor_set_uint8(x_58, 10, x_53);
lean_ctor_set_uint8(x_58, 11, x_54);
lean_ctor_set_uint8(x_58, 12, x_55);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_42);
lean_ctor_set(x_59, 2, x_43);
lean_ctor_set(x_59, 3, x_44);
lean_ctor_set(x_59, 4, x_45);
x_60 = lean_apply_5(x_1, x_59, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_approxDefEqImp___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
x_26 = lean_ctor_get_uint8(x_9, 8);
x_27 = lean_ctor_get_uint8(x_9, 9);
x_28 = lean_ctor_get_uint8(x_9, 10);
x_29 = lean_ctor_get_uint8(x_9, 11);
x_30 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, 3, x_21);
lean_ctor_set_uint8(x_32, 4, x_22);
lean_ctor_set_uint8(x_32, 5, x_23);
lean_ctor_set_uint8(x_32, 6, x_24);
lean_ctor_set_uint8(x_32, 7, x_25);
lean_ctor_set_uint8(x_32, 8, x_26);
lean_ctor_set_uint8(x_32, 9, x_27);
lean_ctor_set_uint8(x_32, 10, x_28);
lean_ctor_set_uint8(x_32, 11, x_29);
lean_ctor_set_uint8(x_32, 12, x_30);
lean_ctor_set(x_3, 0, x_32);
x_33 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_ctor_get(x_3, 1);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_ctor_get(x_3, 3);
x_46 = lean_ctor_get(x_3, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_3);
x_47 = lean_ctor_get_uint8(x_42, 3);
x_48 = lean_ctor_get_uint8(x_42, 4);
x_49 = lean_ctor_get_uint8(x_42, 5);
x_50 = lean_ctor_get_uint8(x_42, 6);
x_51 = lean_ctor_get_uint8(x_42, 7);
x_52 = lean_ctor_get_uint8(x_42, 8);
x_53 = lean_ctor_get_uint8(x_42, 9);
x_54 = lean_ctor_get_uint8(x_42, 10);
x_55 = lean_ctor_get_uint8(x_42, 11);
x_56 = lean_ctor_get_uint8(x_42, 12);
if (lean_is_exclusive(x_42)) {
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = 1;
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 0, 13);
} else {
 x_59 = x_57;
}
lean_ctor_set_uint8(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, 2, x_58);
lean_ctor_set_uint8(x_59, 3, x_47);
lean_ctor_set_uint8(x_59, 4, x_48);
lean_ctor_set_uint8(x_59, 5, x_49);
lean_ctor_set_uint8(x_59, 6, x_50);
lean_ctor_set_uint8(x_59, 7, x_51);
lean_ctor_set_uint8(x_59, 8, x_52);
lean_ctor_set_uint8(x_59, 9, x_53);
lean_ctor_set_uint8(x_59, 10, x_54);
lean_ctor_set_uint8(x_59, 11, x_55);
lean_ctor_set_uint8(x_59, 12, x_56);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
lean_ctor_set(x_60, 2, x_44);
lean_ctor_set(x_60, 3, x_45);
lean_ctor_set(x_60, 4, x_46);
x_61 = lean_apply_7(x_2, lean_box(0), x_1, x_60, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_approxDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_approxDefEq___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get_uint8(x_8, 4);
x_21 = lean_ctor_get_uint8(x_8, 5);
x_22 = lean_ctor_get_uint8(x_8, 6);
x_23 = lean_ctor_get_uint8(x_8, 7);
x_24 = lean_ctor_get_uint8(x_8, 8);
x_25 = lean_ctor_get_uint8(x_8, 9);
x_26 = lean_ctor_get_uint8(x_8, 10);
x_27 = lean_ctor_get_uint8(x_8, 11);
x_28 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, 2, x_29);
lean_ctor_set_uint8(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, 4, x_20);
lean_ctor_set_uint8(x_30, 5, x_21);
lean_ctor_set_uint8(x_30, 6, x_22);
lean_ctor_set_uint8(x_30, 7, x_23);
lean_ctor_set_uint8(x_30, 8, x_24);
lean_ctor_set_uint8(x_30, 9, x_25);
lean_ctor_set_uint8(x_30, 10, x_26);
lean_ctor_set_uint8(x_30, 11, x_27);
lean_ctor_set_uint8(x_30, 12, x_28);
lean_ctor_set(x_2, 0, x_30);
x_31 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_45 = lean_ctor_get_uint8(x_40, 4);
x_46 = lean_ctor_get_uint8(x_40, 5);
x_47 = lean_ctor_get_uint8(x_40, 6);
x_48 = lean_ctor_get_uint8(x_40, 7);
x_49 = lean_ctor_get_uint8(x_40, 8);
x_50 = lean_ctor_get_uint8(x_40, 9);
x_51 = lean_ctor_get_uint8(x_40, 10);
x_52 = lean_ctor_get_uint8(x_40, 11);
x_53 = lean_ctor_get_uint8(x_40, 12);
if (lean_is_exclusive(x_40)) {
 x_54 = x_40;
} else {
 lean_dec_ref(x_40);
 x_54 = lean_box(0);
}
x_55 = 1;
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 0, 13);
} else {
 x_56 = x_54;
}
lean_ctor_set_uint8(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, 3, x_55);
lean_ctor_set_uint8(x_56, 4, x_45);
lean_ctor_set_uint8(x_56, 5, x_46);
lean_ctor_set_uint8(x_56, 6, x_47);
lean_ctor_set_uint8(x_56, 7, x_48);
lean_ctor_set_uint8(x_56, 8, x_49);
lean_ctor_set_uint8(x_56, 9, x_50);
lean_ctor_set_uint8(x_56, 10, x_51);
lean_ctor_set_uint8(x_56, 11, x_52);
lean_ctor_set_uint8(x_56, 12, x_53);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set(x_57, 4, x_44);
x_58 = lean_apply_5(x_1, x_57, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_fullApproxDefEqImp___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get_uint8(x_9, 4);
x_22 = lean_ctor_get_uint8(x_9, 5);
x_23 = lean_ctor_get_uint8(x_9, 6);
x_24 = lean_ctor_get_uint8(x_9, 7);
x_25 = lean_ctor_get_uint8(x_9, 8);
x_26 = lean_ctor_get_uint8(x_9, 9);
x_27 = lean_ctor_get_uint8(x_9, 10);
x_28 = lean_ctor_get_uint8(x_9, 11);
x_29 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, 4, x_21);
lean_ctor_set_uint8(x_31, 5, x_22);
lean_ctor_set_uint8(x_31, 6, x_23);
lean_ctor_set_uint8(x_31, 7, x_24);
lean_ctor_set_uint8(x_31, 8, x_25);
lean_ctor_set_uint8(x_31, 9, x_26);
lean_ctor_set_uint8(x_31, 10, x_27);
lean_ctor_set_uint8(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, 12, x_29);
lean_ctor_set(x_3, 0, x_31);
x_32 = lean_apply_7(x_2, lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_ctor_get(x_3, 3);
x_45 = lean_ctor_get(x_3, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_3);
x_46 = lean_ctor_get_uint8(x_41, 4);
x_47 = lean_ctor_get_uint8(x_41, 5);
x_48 = lean_ctor_get_uint8(x_41, 6);
x_49 = lean_ctor_get_uint8(x_41, 7);
x_50 = lean_ctor_get_uint8(x_41, 8);
x_51 = lean_ctor_get_uint8(x_41, 9);
x_52 = lean_ctor_get_uint8(x_41, 10);
x_53 = lean_ctor_get_uint8(x_41, 11);
x_54 = lean_ctor_get_uint8(x_41, 12);
if (lean_is_exclusive(x_41)) {
 x_55 = x_41;
} else {
 lean_dec_ref(x_41);
 x_55 = lean_box(0);
}
x_56 = 1;
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 0, 13);
} else {
 x_57 = x_55;
}
lean_ctor_set_uint8(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, 2, x_56);
lean_ctor_set_uint8(x_57, 3, x_56);
lean_ctor_set_uint8(x_57, 4, x_46);
lean_ctor_set_uint8(x_57, 5, x_47);
lean_ctor_set_uint8(x_57, 6, x_48);
lean_ctor_set_uint8(x_57, 7, x_49);
lean_ctor_set_uint8(x_57, 8, x_50);
lean_ctor_set_uint8(x_57, 9, x_51);
lean_ctor_set_uint8(x_57, 10, x_52);
lean_ctor_set_uint8(x_57, 11, x_53);
lean_ctor_set_uint8(x_57, 12, x_54);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 3, x_44);
lean_ctor_set(x_58, 4, x_45);
x_59 = lean_apply_7(x_2, lean_box(0), x_1, x_58, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_fullApproxDefEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_fullApproxDefEq___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Level_normalize(x_9);
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
x_13 = l_Lean_Level_normalize(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normalizeLevel(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assignLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_whnfR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
x_28 = lean_ctor_get_uint8(x_8, 9);
x_29 = lean_ctor_get_uint8(x_8, 10);
x_30 = lean_ctor_get_uint8(x_8, 11);
x_31 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_32 = 2;
x_33 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_33, 0, x_20);
lean_ctor_set_uint8(x_33, 1, x_21);
lean_ctor_set_uint8(x_33, 2, x_22);
lean_ctor_set_uint8(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, 4, x_24);
lean_ctor_set_uint8(x_33, 5, x_32);
lean_ctor_set_uint8(x_33, 6, x_25);
lean_ctor_set_uint8(x_33, 7, x_26);
lean_ctor_set_uint8(x_33, 8, x_27);
lean_ctor_set_uint8(x_33, 9, x_28);
lean_ctor_set_uint8(x_33, 10, x_29);
lean_ctor_set_uint8(x_33, 11, x_30);
lean_ctor_set_uint8(x_33, 12, x_31);
lean_ctor_set(x_2, 0, x_33);
x_34 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_48 = lean_ctor_get_uint8(x_43, 0);
x_49 = lean_ctor_get_uint8(x_43, 1);
x_50 = lean_ctor_get_uint8(x_43, 2);
x_51 = lean_ctor_get_uint8(x_43, 3);
x_52 = lean_ctor_get_uint8(x_43, 4);
x_53 = lean_ctor_get_uint8(x_43, 6);
x_54 = lean_ctor_get_uint8(x_43, 7);
x_55 = lean_ctor_get_uint8(x_43, 8);
x_56 = lean_ctor_get_uint8(x_43, 9);
x_57 = lean_ctor_get_uint8(x_43, 10);
x_58 = lean_ctor_get_uint8(x_43, 11);
x_59 = lean_ctor_get_uint8(x_43, 12);
if (lean_is_exclusive(x_43)) {
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
x_61 = 2;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 0, 13);
} else {
 x_62 = x_60;
}
lean_ctor_set_uint8(x_62, 0, x_48);
lean_ctor_set_uint8(x_62, 1, x_49);
lean_ctor_set_uint8(x_62, 2, x_50);
lean_ctor_set_uint8(x_62, 3, x_51);
lean_ctor_set_uint8(x_62, 4, x_52);
lean_ctor_set_uint8(x_62, 5, x_61);
lean_ctor_set_uint8(x_62, 6, x_53);
lean_ctor_set_uint8(x_62, 7, x_54);
lean_ctor_set_uint8(x_62, 8, x_55);
lean_ctor_set_uint8(x_62, 9, x_56);
lean_ctor_set_uint8(x_62, 10, x_57);
lean_ctor_set_uint8(x_62, 11, x_58);
lean_ctor_set_uint8(x_62, 12, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
x_64 = lean_whnf(x_1, x_63, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
x_28 = lean_ctor_get_uint8(x_8, 9);
x_29 = lean_ctor_get_uint8(x_8, 10);
x_30 = lean_ctor_get_uint8(x_8, 11);
x_31 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_33, 0, x_20);
lean_ctor_set_uint8(x_33, 1, x_21);
lean_ctor_set_uint8(x_33, 2, x_22);
lean_ctor_set_uint8(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, 4, x_24);
lean_ctor_set_uint8(x_33, 5, x_32);
lean_ctor_set_uint8(x_33, 6, x_25);
lean_ctor_set_uint8(x_33, 7, x_26);
lean_ctor_set_uint8(x_33, 8, x_27);
lean_ctor_set_uint8(x_33, 9, x_28);
lean_ctor_set_uint8(x_33, 10, x_29);
lean_ctor_set_uint8(x_33, 11, x_30);
lean_ctor_set_uint8(x_33, 12, x_31);
lean_ctor_set(x_2, 0, x_33);
x_34 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_48 = lean_ctor_get_uint8(x_43, 0);
x_49 = lean_ctor_get_uint8(x_43, 1);
x_50 = lean_ctor_get_uint8(x_43, 2);
x_51 = lean_ctor_get_uint8(x_43, 3);
x_52 = lean_ctor_get_uint8(x_43, 4);
x_53 = lean_ctor_get_uint8(x_43, 6);
x_54 = lean_ctor_get_uint8(x_43, 7);
x_55 = lean_ctor_get_uint8(x_43, 8);
x_56 = lean_ctor_get_uint8(x_43, 9);
x_57 = lean_ctor_get_uint8(x_43, 10);
x_58 = lean_ctor_get_uint8(x_43, 11);
x_59 = lean_ctor_get_uint8(x_43, 12);
if (lean_is_exclusive(x_43)) {
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
x_61 = 1;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 0, 13);
} else {
 x_62 = x_60;
}
lean_ctor_set_uint8(x_62, 0, x_48);
lean_ctor_set_uint8(x_62, 1, x_49);
lean_ctor_set_uint8(x_62, 2, x_50);
lean_ctor_set_uint8(x_62, 3, x_51);
lean_ctor_set_uint8(x_62, 4, x_52);
lean_ctor_set_uint8(x_62, 5, x_61);
lean_ctor_set_uint8(x_62, 6, x_53);
lean_ctor_set_uint8(x_62, 7, x_54);
lean_ctor_set_uint8(x_62, 8, x_55);
lean_ctor_set_uint8(x_62, 9, x_56);
lean_ctor_set_uint8(x_62, 10, x_57);
lean_ctor_set_uint8(x_62, 11, x_58);
lean_ctor_set_uint8(x_62, 12, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
x_64 = lean_whnf(x_1, x_63, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfI(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
x_27 = lean_ctor_get_uint8(x_8, 8);
x_28 = lean_ctor_get_uint8(x_8, 9);
x_29 = lean_ctor_get_uint8(x_8, 10);
x_30 = lean_ctor_get_uint8(x_8, 11);
x_31 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_33, 0, x_20);
lean_ctor_set_uint8(x_33, 1, x_21);
lean_ctor_set_uint8(x_33, 2, x_22);
lean_ctor_set_uint8(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, 4, x_24);
lean_ctor_set_uint8(x_33, 5, x_32);
lean_ctor_set_uint8(x_33, 6, x_25);
lean_ctor_set_uint8(x_33, 7, x_26);
lean_ctor_set_uint8(x_33, 8, x_27);
lean_ctor_set_uint8(x_33, 9, x_28);
lean_ctor_set_uint8(x_33, 10, x_29);
lean_ctor_set_uint8(x_33, 11, x_30);
lean_ctor_set_uint8(x_33, 12, x_31);
lean_ctor_set(x_2, 0, x_33);
x_34 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_48 = lean_ctor_get_uint8(x_43, 0);
x_49 = lean_ctor_get_uint8(x_43, 1);
x_50 = lean_ctor_get_uint8(x_43, 2);
x_51 = lean_ctor_get_uint8(x_43, 3);
x_52 = lean_ctor_get_uint8(x_43, 4);
x_53 = lean_ctor_get_uint8(x_43, 6);
x_54 = lean_ctor_get_uint8(x_43, 7);
x_55 = lean_ctor_get_uint8(x_43, 8);
x_56 = lean_ctor_get_uint8(x_43, 9);
x_57 = lean_ctor_get_uint8(x_43, 10);
x_58 = lean_ctor_get_uint8(x_43, 11);
x_59 = lean_ctor_get_uint8(x_43, 12);
if (lean_is_exclusive(x_43)) {
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
x_61 = 3;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 0, 13);
} else {
 x_62 = x_60;
}
lean_ctor_set_uint8(x_62, 0, x_48);
lean_ctor_set_uint8(x_62, 1, x_49);
lean_ctor_set_uint8(x_62, 2, x_50);
lean_ctor_set_uint8(x_62, 3, x_51);
lean_ctor_set_uint8(x_62, 4, x_52);
lean_ctor_set_uint8(x_62, 5, x_61);
lean_ctor_set_uint8(x_62, 6, x_53);
lean_ctor_set_uint8(x_62, 7, x_54);
lean_ctor_set_uint8(x_62, 8, x_55);
lean_ctor_set_uint8(x_62, 9, x_56);
lean_ctor_set_uint8(x_62, 10, x_57);
lean_ctor_set_uint8(x_62, 11, x_58);
lean_ctor_set_uint8(x_62, 12, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
x_64 = lean_whnf(x_1, x_63, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setInlineAttribute(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_setInlineAttribute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_setInlineAttribute(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_dependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_dependsOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_dependsOn(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_ppExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_6(x_2, x_15, x_3, x_4, x_5, x_6, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_orElse___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instOrElseMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_orElse___rarg), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instOrElseMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instOrElseMetaM___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2;
x_8 = l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_3, x_16, x_4, x_5, x_6, x_7, x_15);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instAlternativeMetaM___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instAlternativeMetaM___lambda__2), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Meta_instAlternativeMetaM___closed__1;
x_4 = l_Lean_Meta_instAlternativeMetaM___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instAlternativeMetaM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instAlternativeMetaM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_instAlternativeMetaM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instAlternativeMetaM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instAlternativeMetaM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_23 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_13, x_5, x_6, x_7, x_8, x_22);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_orelseMergeErrorsImp___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_24 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_14, x_6, x_7, x_8, x_9, x_23);
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
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_orelseMergeErrors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_orelseMergeErrors___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mapErrorImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mapErrorImp___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_mapErrorImp___rarg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mapError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_mapError___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedFVarId;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_local_ctx_find(x_1, x_2);
lean_inc(x_3);
x_5 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Name_quickLt(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = 1;
return x_7;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_LocalDecl_index(x_9);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_index(x_10);
lean_dec(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_15; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_16 = lean_nat_add(x_3, x_4);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
x_87 = l_Lean_instInhabitedFVarId;
x_88 = lean_array_get(x_87, x_2, x_18);
x_89 = lean_array_get(x_87, x_2, x_3);
lean_inc(x_88);
lean_inc(x_1);
x_90 = lean_local_ctx_find(x_1, x_88);
lean_inc(x_89);
lean_inc(x_1);
x_91 = lean_local_ctx_find(x_1, x_89);
if (lean_obj_tag(x_90) == 0)
{
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Name_quickLt(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_92 == 0)
{
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_93; 
x_93 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_93;
goto block_86;
}
}
else
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
x_94 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_94;
goto block_86;
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_90);
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = l_Lean_LocalDecl_index(x_95);
lean_dec(x_95);
x_98 = l_Lean_LocalDecl_index(x_96);
lean_dec(x_96);
x_99 = lean_nat_dec_lt(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_100; 
x_100 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_100;
goto block_86;
}
}
}
block_86:
{
lean_object* x_20; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = l_Lean_instInhabitedFVarId;
x_47 = lean_array_get(x_46, x_19, x_4);
x_71 = lean_array_get(x_46, x_19, x_3);
lean_inc(x_47);
lean_inc(x_1);
x_72 = lean_local_ctx_find(x_1, x_47);
lean_inc(x_71);
lean_inc(x_1);
x_73 = lean_local_ctx_find(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Name_quickLt(x_47, x_71);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_48 = x_75;
goto block_70;
}
else
{
lean_object* x_76; 
lean_dec(x_47);
x_76 = lean_box(0);
x_20 = x_76;
goto block_45;
}
}
else
{
lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_47);
x_77 = lean_box(0);
x_20 = x_77;
goto block_45;
}
}
else
{
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_78; 
lean_dec(x_72);
x_78 = lean_box(0);
x_48 = x_78;
goto block_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = l_Lean_LocalDecl_index(x_79);
lean_dec(x_79);
x_82 = l_Lean_LocalDecl_index(x_80);
lean_dec(x_80);
x_83 = lean_nat_dec_lt(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_48 = x_84;
goto block_70;
}
else
{
lean_object* x_85; 
lean_dec(x_47);
x_85 = lean_box(0);
x_20 = x_85;
goto block_45;
}
}
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_21 = lean_array_swap(x_19, x_3, x_4);
x_22 = l_Lean_instInhabitedFVarId;
x_23 = lean_array_get(x_22, x_21, x_18);
x_24 = lean_array_get(x_22, x_21, x_4);
lean_inc(x_23);
lean_inc(x_1);
x_25 = lean_local_ctx_find(x_1, x_23);
lean_inc(x_24);
lean_inc(x_1);
x_26 = lean_local_ctx_find(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Name_quickLt(x_23, x_24);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_28 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_28;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_29 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_30 = lean_array_get(x_22, x_29, x_4);
lean_inc_n(x_3, 2);
x_31 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_30, x_29, x_3, x_3);
x_6 = x_31;
goto block_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_33 = lean_array_get(x_22, x_32, x_4);
lean_inc_n(x_3, 2);
x_34 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_33, x_32, x_3, x_3);
x_6 = x_34;
goto block_14;
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_35 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_35;
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = l_Lean_LocalDecl_index(x_36);
lean_dec(x_36);
x_39 = l_Lean_LocalDecl_index(x_37);
lean_dec(x_37);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_41 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_41;
goto block_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
x_42 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_43 = lean_array_get(x_22, x_42, x_4);
lean_inc_n(x_3, 2);
x_44 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_43, x_42, x_3, x_3);
x_6 = x_44;
goto block_14;
}
}
}
}
block_70:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_49 = lean_array_get(x_46, x_19, x_18);
lean_inc(x_49);
lean_inc(x_1);
x_50 = lean_local_ctx_find(x_1, x_49);
lean_inc(x_47);
lean_inc(x_1);
x_51 = lean_local_ctx_find(x_1, x_47);
if (lean_obj_tag(x_50) == 0)
{
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Name_quickLt(x_49, x_47);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_53 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_53;
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
x_54 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_55 = lean_array_get(x_46, x_54, x_4);
lean_inc_n(x_3, 2);
x_56 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_55, x_54, x_3, x_3);
x_6 = x_56;
goto block_14;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_47);
x_57 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_58 = lean_array_get(x_46, x_57, x_4);
lean_inc_n(x_3, 2);
x_59 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_58, x_57, x_3, x_3);
x_6 = x_59;
goto block_14;
}
}
else
{
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_60; 
lean_dec(x_50);
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_60 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_60;
goto block_14;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_63 = l_Lean_LocalDecl_index(x_61);
lean_dec(x_61);
x_64 = l_Lean_LocalDecl_index(x_62);
lean_dec(x_62);
x_65 = lean_nat_dec_lt(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_66 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_66;
goto block_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_47);
x_67 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_68 = lean_array_get(x_46, x_67, x_4);
lean_inc_n(x_3, 2);
x_69 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_5, x_4, x_68, x_67, x_3, x_3);
x_6 = x_69;
goto block_14;
}
}
}
}
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1(x_1, x_8, x_3, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_sortFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1(x_7, x_1, x_11, x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Meta_sortFVarIds___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_sortFVarIds___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_sortFVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_sortFVarIds(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
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
lean_object* initialize_Lean_Util_MonadBacktrack(lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(lean_object*);
lean_object* initialize_Lean_Meta_TransparencyMode(lean_object*);
lean_object* initialize_Lean_Meta_DiscrTreeTypes(lean_object*);
lean_object* initialize_Lean_Eval(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Basic(lean_object* w) {
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
res = initialize_Lean_Util_MonadBacktrack(lean_io_mk_world());
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
l_Lean_Meta_Config_proofIrrelevance___default = _init_l_Lean_Meta_Config_proofIrrelevance___default();
l_Lean_Meta_Config_assignSyntheticOpaque___default = _init_l_Lean_Meta_Config_assignSyntheticOpaque___default();
l_Lean_Meta_Config_ignoreLevelMVarDepth___default = _init_l_Lean_Meta_Config_ignoreLevelMVarDepth___default();
l_Lean_Meta_Config_offsetCnstrs___default = _init_l_Lean_Meta_Config_offsetCnstrs___default();
l_Lean_Meta_ParamInfo_binderInfo___default = _init_l_Lean_Meta_ParamInfo_binderInfo___default();
l_Lean_Meta_ParamInfo_hasFwdDeps___default = _init_l_Lean_Meta_ParamInfo_hasFwdDeps___default();
l_Lean_Meta_ParamInfo_backDeps___default___closed__1 = _init_l_Lean_Meta_ParamInfo_backDeps___default___closed__1();
lean_mark_persistent(l_Lean_Meta_ParamInfo_backDeps___default___closed__1);
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
l_Lean_Meta_instInhabitedInfoCacheKey___closed__2 = _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedInfoCacheKey___closed__2);
l_Lean_Meta_instInhabitedInfoCacheKey___closed__3 = _init_l_Lean_Meta_instInhabitedInfoCacheKey___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedInfoCacheKey___closed__3);
l_Lean_Meta_instInhabitedInfoCacheKey = _init_l_Lean_Meta_instInhabitedInfoCacheKey();
lean_mark_persistent(l_Lean_Meta_instInhabitedInfoCacheKey);
l_Lean_Meta_instBEqInfoCacheKey___closed__1 = _init_l_Lean_Meta_instBEqInfoCacheKey___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqInfoCacheKey___closed__1);
l_Lean_Meta_instBEqInfoCacheKey = _init_l_Lean_Meta_instBEqInfoCacheKey();
lean_mark_persistent(l_Lean_Meta_instBEqInfoCacheKey);
l_Lean_Meta_Cache_inferType___default___closed__1 = _init_l_Lean_Meta_Cache_inferType___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Cache_inferType___default___closed__1);
l_Lean_Meta_Cache_inferType___default___closed__2 = _init_l_Lean_Meta_Cache_inferType___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Cache_inferType___default___closed__2);
l_Lean_Meta_Cache_inferType___default___closed__3 = _init_l_Lean_Meta_Cache_inferType___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Cache_inferType___default___closed__3);
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
l_Lean_Meta_Cache_defEqDefault___default___closed__1 = _init_l_Lean_Meta_Cache_defEqDefault___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Cache_defEqDefault___default___closed__1);
l_Lean_Meta_Cache_defEqDefault___default___closed__2 = _init_l_Lean_Meta_Cache_defEqDefault___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Cache_defEqDefault___default___closed__2);
l_Lean_Meta_Cache_defEqDefault___default___closed__3 = _init_l_Lean_Meta_Cache_defEqDefault___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Cache_defEqDefault___default___closed__3);
l_Lean_Meta_Cache_defEqDefault___default = _init_l_Lean_Meta_Cache_defEqDefault___default();
lean_mark_persistent(l_Lean_Meta_Cache_defEqDefault___default);
l_Lean_Meta_Cache_defEqAll___default = _init_l_Lean_Meta_Cache_defEqAll___default();
lean_mark_persistent(l_Lean_Meta_Cache_defEqAll___default);
l_Lean_Meta_instInhabitedCache___closed__1 = _init_l_Lean_Meta_instInhabitedCache___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCache___closed__1);
l_Lean_Meta_instInhabitedCache___closed__2 = _init_l_Lean_Meta_instInhabitedCache___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedCache___closed__2);
l_Lean_Meta_instInhabitedCache = _init_l_Lean_Meta_instInhabitedCache();
lean_mark_persistent(l_Lean_Meta_instInhabitedCache);
l_Lean_Meta_instInhabitedPostponedEntry___closed__1 = _init_l_Lean_Meta_instInhabitedPostponedEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedPostponedEntry___closed__1);
l_Lean_Meta_instInhabitedPostponedEntry___closed__2 = _init_l_Lean_Meta_instInhabitedPostponedEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedPostponedEntry___closed__2);
l_Lean_Meta_instInhabitedPostponedEntry = _init_l_Lean_Meta_instInhabitedPostponedEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedPostponedEntry);
l_Lean_Meta_State_mctx___default___closed__1 = _init_l_Lean_Meta_State_mctx___default___closed__1();
lean_mark_persistent(l_Lean_Meta_State_mctx___default___closed__1);
l_Lean_Meta_State_mctx___default___closed__2 = _init_l_Lean_Meta_State_mctx___default___closed__2();
lean_mark_persistent(l_Lean_Meta_State_mctx___default___closed__2);
l_Lean_Meta_State_mctx___default = _init_l_Lean_Meta_State_mctx___default();
lean_mark_persistent(l_Lean_Meta_State_mctx___default);
l_Lean_Meta_State_cache___default = _init_l_Lean_Meta_State_cache___default();
lean_mark_persistent(l_Lean_Meta_State_cache___default);
l_Lean_Meta_State_zetaFVarIds___default = _init_l_Lean_Meta_State_zetaFVarIds___default();
lean_mark_persistent(l_Lean_Meta_State_zetaFVarIds___default);
l_Lean_Meta_State_postponed___default___closed__1 = _init_l_Lean_Meta_State_postponed___default___closed__1();
lean_mark_persistent(l_Lean_Meta_State_postponed___default___closed__1);
l_Lean_Meta_State_postponed___default___closed__2 = _init_l_Lean_Meta_State_postponed___default___closed__2();
lean_mark_persistent(l_Lean_Meta_State_postponed___default___closed__2);
l_Lean_Meta_State_postponed___default___closed__3 = _init_l_Lean_Meta_State_postponed___default___closed__3();
lean_mark_persistent(l_Lean_Meta_State_postponed___default___closed__3);
l_Lean_Meta_State_postponed___default = _init_l_Lean_Meta_State_postponed___default();
lean_mark_persistent(l_Lean_Meta_State_postponed___default);
l_Lean_Meta_instInhabitedState___closed__1 = _init_l_Lean_Meta_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedState___closed__1);
l_Lean_Meta_instInhabitedState___closed__2 = _init_l_Lean_Meta_instInhabitedState___closed__2();
l_Lean_Meta_instInhabitedState___closed__3 = _init_l_Lean_Meta_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedState___closed__3);
l_Lean_Meta_instInhabitedState___closed__4 = _init_l_Lean_Meta_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedState___closed__4);
l_Lean_Meta_instInhabitedState = _init_l_Lean_Meta_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_instInhabitedState);
l_Lean_Meta_instInhabitedSavedState___closed__1 = _init_l_Lean_Meta_instInhabitedSavedState___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__1);
l_Lean_Meta_instInhabitedSavedState___closed__2 = _init_l_Lean_Meta_instInhabitedSavedState___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__2);
l_Lean_Meta_instInhabitedSavedState___closed__3 = _init_l_Lean_Meta_instInhabitedSavedState___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__3);
l_Lean_Meta_instInhabitedSavedState___closed__4 = _init_l_Lean_Meta_instInhabitedSavedState___closed__4();
l_Lean_Meta_instInhabitedSavedState___closed__5 = _init_l_Lean_Meta_instInhabitedSavedState___closed__5();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__5);
l_Lean_Meta_instInhabitedSavedState___closed__6 = _init_l_Lean_Meta_instInhabitedSavedState___closed__6();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__6);
l_Lean_Meta_instInhabitedSavedState___closed__7 = _init_l_Lean_Meta_instInhabitedSavedState___closed__7();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__7);
l_Lean_Meta_instInhabitedSavedState___closed__8 = _init_l_Lean_Meta_instInhabitedSavedState___closed__8();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__8);
l_Lean_Meta_instInhabitedSavedState___closed__9 = _init_l_Lean_Meta_instInhabitedSavedState___closed__9();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__9);
l_Lean_Meta_instInhabitedSavedState___closed__10 = _init_l_Lean_Meta_instInhabitedSavedState___closed__10();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__10);
l_Lean_Meta_instInhabitedSavedState___closed__11 = _init_l_Lean_Meta_instInhabitedSavedState___closed__11();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState___closed__11);
l_Lean_Meta_instInhabitedSavedState = _init_l_Lean_Meta_instInhabitedSavedState();
lean_mark_persistent(l_Lean_Meta_instInhabitedSavedState);
l_Lean_Meta_Context_config___default___closed__1 = _init_l_Lean_Meta_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Context_config___default___closed__1);
l_Lean_Meta_Context_config___default = _init_l_Lean_Meta_Context_config___default();
lean_mark_persistent(l_Lean_Meta_Context_config___default);
l_Lean_Meta_Context_lctx___default___closed__1 = _init_l_Lean_Meta_Context_lctx___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Context_lctx___default___closed__1);
l_Lean_Meta_Context_lctx___default___closed__2 = _init_l_Lean_Meta_Context_lctx___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Context_lctx___default___closed__2);
l_Lean_Meta_Context_lctx___default = _init_l_Lean_Meta_Context_lctx___default();
lean_mark_persistent(l_Lean_Meta_Context_lctx___default);
l_Lean_Meta_Context_localInstances___default = _init_l_Lean_Meta_Context_localInstances___default();
lean_mark_persistent(l_Lean_Meta_Context_localInstances___default);
l_Lean_Meta_Context_defEqCtx_x3f___default = _init_l_Lean_Meta_Context_defEqCtx_x3f___default();
lean_mark_persistent(l_Lean_Meta_Context_defEqCtx_x3f___default);
l_Lean_Meta_Context_synthPendingDepth___default = _init_l_Lean_Meta_Context_synthPendingDepth___default();
lean_mark_persistent(l_Lean_Meta_Context_synthPendingDepth___default);
l_Lean_Meta_instMonadMetaM___closed__1 = _init_l_Lean_Meta_instMonadMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM___closed__1);
l_Lean_Meta_instMonadMetaM___closed__2 = _init_l_Lean_Meta_instMonadMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM___closed__2);
l_Lean_Meta_instMonadMetaM___closed__3 = _init_l_Lean_Meta_instMonadMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM___closed__3);
l_Lean_Meta_instMonadMetaM___closed__4 = _init_l_Lean_Meta_instMonadMetaM___closed__4();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM___closed__4);
l_Lean_Meta_instMonadMetaM___closed__5 = _init_l_Lean_Meta_instMonadMetaM___closed__5();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM___closed__5);
l_Lean_Meta_instMonadMetaM = _init_l_Lean_Meta_instMonadMetaM();
lean_mark_persistent(l_Lean_Meta_instMonadMetaM);
l_Lean_Meta_instInhabitedMetaM___rarg___closed__1 = _init_l_Lean_Meta_instInhabitedMetaM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedMetaM___rarg___closed__1);
l_Lean_Meta_instInhabitedMetaM___rarg___closed__2 = _init_l_Lean_Meta_instInhabitedMetaM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedMetaM___rarg___closed__2);
l_Lean_Meta_instMonadMCtxMetaM___closed__1 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__1);
l_Lean_Meta_instMonadMCtxMetaM___closed__2 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__2);
l_Lean_Meta_instMonadMCtxMetaM___closed__3 = _init_l_Lean_Meta_instMonadMCtxMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM___closed__3);
l_Lean_Meta_instMonadMCtxMetaM = _init_l_Lean_Meta_instMonadMCtxMetaM();
lean_mark_persistent(l_Lean_Meta_instMonadMCtxMetaM);
l_Lean_Meta_instAddMessageContextMetaM___closed__1 = _init_l_Lean_Meta_instAddMessageContextMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instAddMessageContextMetaM___closed__1);
l_Lean_Meta_instAddMessageContextMetaM = _init_l_Lean_Meta_instAddMessageContextMetaM();
lean_mark_persistent(l_Lean_Meta_instAddMessageContextMetaM);
l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1 = _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__1);
l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2 = _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__2);
l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3 = _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instMonadBacktrackSavedStateMetaM___closed__3);
l_Lean_Meta_instMonadBacktrackSavedStateMetaM = _init_l_Lean_Meta_instMonadBacktrackSavedStateMetaM();
lean_mark_persistent(l_Lean_Meta_instMonadBacktrackSavedStateMetaM);
l_Lean_Meta_MetaM_toIO___rarg___closed__1 = _init_l_Lean_Meta_MetaM_toIO___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_MetaM_toIO___rarg___closed__1);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__1);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__2);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__3);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__4);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__5);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__6);
l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7 = _init_l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_instMetaEvalMetaM___rarg___closed__7);
l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1 = _init_l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIsDefEqStuck___rarg___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134____closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1134_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__1);
l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2 = _init_l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___rarg___lambda__2___closed__2);
l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__2);
l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__3);
l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1___closed__4);
l_Lean_Meta_getMVarDecl___closed__1 = _init_l_Lean_Meta_getMVarDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___closed__1);
l_Lean_Meta_getMVarDecl___closed__2 = _init_l_Lean_Meta_getMVarDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_getMVarDecl___closed__2);
l_Lean_Meta_getLevelMVarDepth___closed__1 = _init_l_Lean_Meta_getLevelMVarDepth___closed__1();
lean_mark_persistent(l_Lean_Meta_getLevelMVarDepth___closed__1);
l_Lean_Meta_getLevelMVarDepth___closed__2 = _init_l_Lean_Meta_getLevelMVarDepth___closed__2();
lean_mark_persistent(l_Lean_Meta_getLevelMVarDepth___closed__2);
l_Lean_Meta_throwUnknownFVar___rarg___closed__1 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__1);
l_Lean_Meta_throwUnknownFVar___rarg___closed__2 = _init_l_Lean_Meta_throwUnknownFVar___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwUnknownFVar___rarg___closed__2);
l_Lean_Meta_getLocalDeclFromUserName___closed__1 = _init_l_Lean_Meta_getLocalDeclFromUserName___closed__1();
lean_mark_persistent(l_Lean_Meta_getLocalDeclFromUserName___closed__1);
l_Lean_Meta_getLocalDeclFromUserName___closed__2 = _init_l_Lean_Meta_getLocalDeclFromUserName___closed__2();
lean_mark_persistent(l_Lean_Meta_getLocalDeclFromUserName___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_instantiateMVars___spec__5___boxed__const__1);
l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1 = _init_l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_instantiateExprMVars___at_Lean_Meta_instantiateMVars___spec__1___closed__1);
l_Lean_Meta_liftMkBindingM___rarg___closed__1 = _init_l_Lean_Meta_liftMkBindingM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_liftMkBindingM___rarg___closed__1);
l_Lean_Meta_liftMkBindingM___rarg___closed__2 = _init_l_Lean_Meta_liftMkBindingM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_liftMkBindingM___rarg___closed__2);
l_Lean_Meta_mkArrow___closed__1 = _init_l_Lean_Meta_mkArrow___closed__1();
lean_mark_persistent(l_Lean_Meta_mkArrow___closed__1);
l_Lean_Meta_mkArrow___closed__2 = _init_l_Lean_Meta_mkArrow___closed__2();
lean_mark_persistent(l_Lean_Meta_mkArrow___closed__2);
l_Lean_Meta_mkFunUnit___closed__1 = _init_l_Lean_Meta_mkFunUnit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFunUnit___closed__1);
l_Lean_Meta_mkFunUnit___closed__2 = _init_l_Lean_Meta_mkFunUnit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkFunUnit___closed__2);
l_Lean_Meta_mkFunUnit___closed__3 = _init_l_Lean_Meta_mkFunUnit___closed__3();
lean_mark_persistent(l_Lean_Meta_mkFunUnit___closed__3);
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
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__1);
l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2 = _init_l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux___closed__2);
l_Lean_Meta_instOrElseMetaM___closed__1 = _init_l_Lean_Meta_instOrElseMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instOrElseMetaM___closed__1);
l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1 = _init_l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__1);
l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2 = _init_l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM___lambda__1___closed__2);
l_Lean_Meta_instAlternativeMetaM___closed__1 = _init_l_Lean_Meta_instAlternativeMetaM___closed__1();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM___closed__1);
l_Lean_Meta_instAlternativeMetaM___closed__2 = _init_l_Lean_Meta_instAlternativeMetaM___closed__2();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM___closed__2);
l_Lean_Meta_instAlternativeMetaM___closed__3 = _init_l_Lean_Meta_instAlternativeMetaM___closed__3();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM___closed__3);
l_Lean_Meta_instAlternativeMetaM = _init_l_Lean_Meta_instAlternativeMetaM();
lean_mark_persistent(l_Lean_Meta_instAlternativeMetaM);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
