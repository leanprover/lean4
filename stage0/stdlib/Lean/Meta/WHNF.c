// Lean compiler output
// Module: Lean.Meta.WHNF
// Imports: Lean.Structure Lean.Util.Recognizers Lean.Util.SafeExponentiation Lean.Meta.GetUnfoldableConst Lean.Meta.FunInfo Lean.Meta.Offset Lean.Meta.CtorRecognizer Lean.Meta.Match.MatcherInfo Lean.Meta.Match.MatchPatternAttr Lean.Meta.Transform
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cleanupNatOffsetMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStructuralRecArgPos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__8;
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__3;
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_useEtaStruct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
lean_object* l_Lean_Meta_getTransparency___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__5;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatchAlt(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__16;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__20;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatch___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_instance(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lam__0___boxed(lean_object*);
lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__28;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__3;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__27;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingSuffix;
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
static uint64_t l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfolding;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__6;
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_;
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_gcd___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_recordUnfold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIrreducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfAtMostI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__4;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__25;
static lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__19;
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__10;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_whnfCore_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f___boxed(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_;
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldDefinition_x3f___closed__0;
static double l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0;
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__24;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatch(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__9;
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__8;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__20;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__31;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT uint8_t l_Lean_Meta_whnfEasyCases___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__26;
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__1;
static lean_object* l_Lean_Meta_smartUnfoldingSuffix___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__7;
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_unfoldProjInst_x3f___closed__0;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__26;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldDefinition___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatch___closed__1;
static lean_object* l_Lean_Meta_reducePow___closed__0;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_;
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__0;
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__1;
static lean_object* l_Lean_Meta_reducePow___closed__1;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__17;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hasSmartUnfoldingDecl___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__18;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_withNatValue___redArg___closed__0;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__19;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__27;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__18;
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__2;
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__23;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__22;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNatNativeUnsafe___closed__0;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__12;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__7;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__15;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__13;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldProjInstWhenInstances_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatSucc(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__32;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_36_(lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__33;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__30;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_;
static lean_object* l_Lean_Meta_unfoldDefinition___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__1;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
static uint64_t l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__13;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letFunAppArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_;
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__9;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__8;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__2;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0(lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_10892_(lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__22;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__7;
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__3;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__6;
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__10;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_get_structural_rec_arg_pos(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__9;
lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__25;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldDefinition___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_;
static lean_object* l_Lean_Meta_whnfEasyCases___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f___boxed(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getStructuralRecArgPos_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_get_structural_rec_arg_pos(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_smartUnfoldingSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_sunfold", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_smartUnfoldingSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
x_4 = l_Lean_Name_str___override(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Environment_contains(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasSmartUnfoldingDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_hasSmartUnfoldingDecl(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("smartUnfolding", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("when computing weak head normal form, use auxiliary definition created for functions defined by structural recursion", 116, 116);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_36_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sunfoldMatch", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markSmartUnfoldingMatch___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatch___closed__1;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatch___closed__1;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_smartUnfoldingMatch_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sunfoldMatchAlt", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_smartUnfoldingMatchAlt_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_is_aux_recursor(x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_is_no_confusion(x_7, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_14);
x_15 = lean_is_aux_recursor(x_14, x_1);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_is_no_confusion(x_14, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_1);
x_19 = lean_box(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isAuxDef___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isAuxDef___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isAuxDef(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_2 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getUnfoldableConst_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_st_ref_get(x_6, x_7);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Environment_find_x3f(x_12, x_1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Environment_find_x3f(x_18, x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_2 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUnfoldableConstNoEx_x3f___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_st_ref_get(x_5, x_6);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Environment_find_x3f(x_11, x_1, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Environment_find_x3f(x_17, x_1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_apply_6(x_2, x_15, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_apply_7(x_3, x_18, x_11, x_5, x_6, x_7, x_8, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_apply_6(x_2, x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_13 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_3, x_16, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_apply_7(x_4, x_19, x_12, x_6, x_7, x_8, x_9, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_6(x_3, x_25, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_2, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Environment_find_x3f(x_12, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_free_object(x_8);
x_4 = x_11;
goto block_7;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_free_object(x_15);
lean_free_object(x_8);
x_4 = x_11;
goto block_7;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_20);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
}
else
{
lean_free_object(x_15);
lean_dec(x_17);
lean_free_object(x_8);
x_4 = x_11;
goto block_7;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_free_object(x_8);
x_4 = x_11;
goto block_7;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_dec(x_21);
lean_free_object(x_8);
x_4 = x_11;
goto block_7;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Environment_find_x3f(x_28, x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
x_4 = x_27;
goto block_7;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_obj_tag(x_32) == 5)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_33);
x_4 = x_27;
goto block_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_4 = x_27;
goto block_7;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_6, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_1);
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = l_Lean_Expr_const___override(x_19, x_7);
x_21 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_22 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_22);
x_23 = lean_mk_array(x_22, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_22, x_24);
lean_dec(x_22);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_23, x_25);
x_27 = l_Array_shrink___redArg(x_26, x_2);
x_28 = l_Lean_mkAppN(x_20, x_27);
lean_dec(x_27);
lean_ctor_set(x_9, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = l_Lean_Expr_const___override(x_29, x_7);
x_31 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_32 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_32);
x_33 = lean_mk_array(x_32, x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_32, x_34);
lean_dec(x_32);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_35);
x_37 = l_Array_shrink___redArg(x_36, x_2);
x_38 = l_Lean_mkAppN(x_30, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_8, 0, x_39);
return x_8;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_42 = x_9;
} else {
 lean_dec_ref(x_9);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Expr_const___override(x_41, x_7);
x_44 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_45 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_45);
x_46 = lean_mk_array(x_45, x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_45, x_47);
lean_dec(x_45);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_46, x_48);
x_50 = l_Array_shrink___redArg(x_49, x_2);
x_51 = l_Lean_mkAppN(x_43, x_50);
lean_dec(x_50);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 6);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_List_find_x3f___redArg(x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_hasExprMVar(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_124; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_124 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_127 = lean_whnf(x_125, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_156; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
x_131 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_129, x_4, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_159 = l_Lean_Expr_getAppFn(x_132);
lean_inc(x_1);
x_160 = l_Lean_RecursorVal_getMajorInduct(x_1);
x_161 = l_Lean_Expr_isConstOf(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
if (x_161 == 0)
{
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_127, 1, x_133);
lean_ctor_set(x_127, 0, x_2);
return x_127;
}
else
{
uint8_t x_162; 
lean_free_object(x_127);
x_162 = l_Lean_Expr_hasExprMVar(x_132);
if (x_162 == 0)
{
x_156 = x_162;
goto block_158;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_183; 
x_163 = lean_ctor_get(x_1, 2);
lean_inc(x_163);
x_164 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_165 = l_Lean_Expr_getAppNumArgs(x_132);
lean_inc(x_165);
x_166 = lean_mk_array(x_165, x_164);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_165, x_167);
lean_dec(x_165);
lean_inc(x_132);
x_169 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_132, x_166, x_168);
x_170 = lean_array_get_size(x_169);
x_171 = l_Array_toSubarray___redArg(x_169, x_163, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_box(0);
x_183 = lean_nat_dec_lt(x_173, x_174);
if (x_183 == 0)
{
uint8_t x_184; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_134);
x_184 = lean_unbox(x_175);
x_135 = x_184;
goto block_155;
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_array_get_size(x_172);
x_186 = lean_nat_dec_le(x_174, x_185);
if (x_186 == 0)
{
lean_dec(x_174);
x_176 = x_185;
goto block_182;
}
else
{
lean_dec(x_185);
x_176 = x_174;
goto block_182;
}
}
block_182:
{
uint8_t x_177; 
x_177 = lean_nat_dec_lt(x_173, x_176);
if (x_177 == 0)
{
uint8_t x_178; 
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_134);
x_178 = lean_unbox(x_175);
x_135 = x_178;
goto block_155;
}
else
{
size_t x_179; size_t x_180; uint8_t x_181; 
x_179 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_180 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_181 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0(x_172, x_179, x_180);
lean_dec(x_172);
x_156 = x_181;
goto block_158;
}
}
}
}
block_155:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_1, 2);
lean_inc(x_136);
lean_dec(x_1);
lean_inc(x_132);
x_137 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(x_132, x_136, x_6, x_133);
lean_dec(x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_137, 0);
lean_dec(x_140);
lean_ctor_set(x_137, 0, x_2);
return x_137;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
lean_dec(x_137);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
lean_dec(x_138);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_144);
x_145 = lean_infer_type(x_144, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_146 = lean_ctor_get(x_3, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get_uint8(x_146, 9);
lean_dec(x_146);
x_150 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___lam__0), 7, 2);
lean_closure_set(x_150, 0, x_132);
lean_closure_set(x_150, 1, x_147);
x_151 = lean_box(1);
x_152 = lean_unbox(x_151);
x_153 = l_Lean_Meta_TransparencyMode_lt(x_149, x_152);
if (x_153 == 0)
{
x_8 = x_148;
x_9 = x_150;
x_10 = x_144;
x_11 = x_135;
x_12 = x_149;
goto block_123;
}
else
{
uint8_t x_154; 
x_154 = lean_unbox(x_151);
x_8 = x_148;
x_9 = x_150;
x_10 = x_144;
x_11 = x_135;
x_12 = x_154;
goto block_123;
}
}
else
{
lean_dec(x_144);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_145;
}
}
}
block_158:
{
if (x_156 == 0)
{
lean_dec(x_134);
x_135 = x_156;
goto block_155;
}
else
{
lean_object* x_157; 
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_134)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_134;
}
lean_ctor_set(x_157, 0, x_2);
lean_ctor_set(x_157, 1, x_133);
return x_157;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_213; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_187 = lean_ctor_get(x_127, 0);
x_188 = lean_ctor_get(x_127, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_127);
x_189 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_187, x_4, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_216 = l_Lean_Expr_getAppFn(x_190);
lean_inc(x_1);
x_217 = l_Lean_RecursorVal_getMajorInduct(x_1);
x_218 = l_Lean_Expr_isConstOf(x_216, x_217);
lean_dec(x_217);
lean_dec(x_216);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_2);
lean_ctor_set(x_219, 1, x_191);
return x_219;
}
else
{
uint8_t x_220; 
x_220 = l_Lean_Expr_hasExprMVar(x_190);
if (x_220 == 0)
{
x_213 = x_220;
goto block_215;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_241; 
x_221 = lean_ctor_get(x_1, 2);
lean_inc(x_221);
x_222 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_223 = l_Lean_Expr_getAppNumArgs(x_190);
lean_inc(x_223);
x_224 = lean_mk_array(x_223, x_222);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_sub(x_223, x_225);
lean_dec(x_223);
lean_inc(x_190);
x_227 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_190, x_224, x_226);
x_228 = lean_array_get_size(x_227);
x_229 = l_Array_toSubarray___redArg(x_227, x_221, x_228);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 2);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_box(0);
x_241 = lean_nat_dec_lt(x_231, x_232);
if (x_241 == 0)
{
uint8_t x_242; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_192);
x_242 = lean_unbox(x_233);
x_193 = x_242;
goto block_212;
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_array_get_size(x_230);
x_244 = lean_nat_dec_le(x_232, x_243);
if (x_244 == 0)
{
lean_dec(x_232);
x_234 = x_243;
goto block_240;
}
else
{
lean_dec(x_243);
x_234 = x_232;
goto block_240;
}
}
block_240:
{
uint8_t x_235; 
x_235 = lean_nat_dec_lt(x_231, x_234);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_234);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_192);
x_236 = lean_unbox(x_233);
x_193 = x_236;
goto block_212;
}
else
{
size_t x_237; size_t x_238; uint8_t x_239; 
x_237 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_238 = lean_usize_of_nat(x_234);
lean_dec(x_234);
x_239 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0(x_230, x_237, x_238);
lean_dec(x_230);
x_213 = x_239;
goto block_215;
}
}
}
}
block_212:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_1, 2);
lean_inc(x_194);
lean_dec(x_1);
lean_inc(x_190);
x_195 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg(x_190, x_194, x_6, x_191);
lean_dec(x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_2);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
lean_dec(x_195);
x_201 = lean_ctor_get(x_196, 0);
lean_inc(x_201);
lean_dec(x_196);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_201);
x_202 = lean_infer_type(x_201, x_3, x_4, x_5, x_6, x_200);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; 
x_203 = lean_ctor_get(x_3, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_ctor_get_uint8(x_203, 9);
lean_dec(x_203);
x_207 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___lam__0), 7, 2);
lean_closure_set(x_207, 0, x_190);
lean_closure_set(x_207, 1, x_204);
x_208 = lean_box(1);
x_209 = lean_unbox(x_208);
x_210 = l_Lean_Meta_TransparencyMode_lt(x_206, x_209);
if (x_210 == 0)
{
x_8 = x_205;
x_9 = x_207;
x_10 = x_201;
x_11 = x_193;
x_12 = x_206;
goto block_123;
}
else
{
uint8_t x_211; 
x_211 = lean_unbox(x_208);
x_8 = x_205;
x_9 = x_207;
x_10 = x_201;
x_11 = x_193;
x_12 = x_211;
goto block_123;
}
}
else
{
lean_dec(x_201);
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_202;
}
}
}
block_215:
{
if (x_213 == 0)
{
lean_dec(x_192);
x_193 = x_213;
goto block_212;
}
else
{
lean_object* x_214; 
lean_dec(x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_192)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_192;
}
lean_ctor_set(x_214, 0, x_2);
lean_ctor_set(x_214, 1, x_191);
return x_214;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_127;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_124;
}
block_123:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
lean_ctor_set_uint8(x_14, 9, x_12);
x_17 = 2;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_shift_left(x_18, x_17);
x_20 = l_Lean_Meta_TransparencyMode_toUInt64(x_12);
x_21 = lean_uint64_lor(x_19, x_20);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_21);
x_22 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_9, x_11, x_3, x_4, x_5, x_6, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_ctor_set(x_22, 0, x_10);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint64_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; 
x_37 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_38 = lean_ctor_get_uint8(x_14, 0);
x_39 = lean_ctor_get_uint8(x_14, 1);
x_40 = lean_ctor_get_uint8(x_14, 2);
x_41 = lean_ctor_get_uint8(x_14, 3);
x_42 = lean_ctor_get_uint8(x_14, 4);
x_43 = lean_ctor_get_uint8(x_14, 5);
x_44 = lean_ctor_get_uint8(x_14, 6);
x_45 = lean_ctor_get_uint8(x_14, 7);
x_46 = lean_ctor_get_uint8(x_14, 8);
x_47 = lean_ctor_get_uint8(x_14, 10);
x_48 = lean_ctor_get_uint8(x_14, 11);
x_49 = lean_ctor_get_uint8(x_14, 12);
x_50 = lean_ctor_get_uint8(x_14, 13);
x_51 = lean_ctor_get_uint8(x_14, 14);
x_52 = lean_ctor_get_uint8(x_14, 15);
x_53 = lean_ctor_get_uint8(x_14, 16);
x_54 = lean_ctor_get_uint8(x_14, 17);
lean_dec(x_14);
x_55 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_55, 0, x_38);
lean_ctor_set_uint8(x_55, 1, x_39);
lean_ctor_set_uint8(x_55, 2, x_40);
lean_ctor_set_uint8(x_55, 3, x_41);
lean_ctor_set_uint8(x_55, 4, x_42);
lean_ctor_set_uint8(x_55, 5, x_43);
lean_ctor_set_uint8(x_55, 6, x_44);
lean_ctor_set_uint8(x_55, 7, x_45);
lean_ctor_set_uint8(x_55, 8, x_46);
lean_ctor_set_uint8(x_55, 9, x_12);
lean_ctor_set_uint8(x_55, 10, x_47);
lean_ctor_set_uint8(x_55, 11, x_48);
lean_ctor_set_uint8(x_55, 12, x_49);
lean_ctor_set_uint8(x_55, 13, x_50);
lean_ctor_set_uint8(x_55, 14, x_51);
lean_ctor_set_uint8(x_55, 15, x_52);
lean_ctor_set_uint8(x_55, 16, x_53);
lean_ctor_set_uint8(x_55, 17, x_54);
x_56 = 2;
x_57 = lean_uint64_shift_right(x_37, x_56);
x_58 = lean_uint64_shift_left(x_57, x_56);
x_59 = l_Lean_Meta_TransparencyMode_toUInt64(x_12);
x_60 = lean_uint64_lor(x_58, x_59);
lean_ctor_set(x_3, 0, x_55);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_60);
x_61 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_9, x_11, x_3, x_4, x_5, x_6, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
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
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_10);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_10);
lean_dec(x_2);
x_70 = lean_ctor_get(x_61, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_72 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_object* x_74; uint64_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; 
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_77 = lean_ctor_get(x_3, 1);
x_78 = lean_ctor_get(x_3, 2);
x_79 = lean_ctor_get(x_3, 3);
x_80 = lean_ctor_get(x_3, 4);
x_81 = lean_ctor_get(x_3, 5);
x_82 = lean_ctor_get(x_3, 6);
x_83 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_84 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_74);
lean_dec(x_3);
x_85 = lean_ctor_get_uint8(x_74, 0);
x_86 = lean_ctor_get_uint8(x_74, 1);
x_87 = lean_ctor_get_uint8(x_74, 2);
x_88 = lean_ctor_get_uint8(x_74, 3);
x_89 = lean_ctor_get_uint8(x_74, 4);
x_90 = lean_ctor_get_uint8(x_74, 5);
x_91 = lean_ctor_get_uint8(x_74, 6);
x_92 = lean_ctor_get_uint8(x_74, 7);
x_93 = lean_ctor_get_uint8(x_74, 8);
x_94 = lean_ctor_get_uint8(x_74, 10);
x_95 = lean_ctor_get_uint8(x_74, 11);
x_96 = lean_ctor_get_uint8(x_74, 12);
x_97 = lean_ctor_get_uint8(x_74, 13);
x_98 = lean_ctor_get_uint8(x_74, 14);
x_99 = lean_ctor_get_uint8(x_74, 15);
x_100 = lean_ctor_get_uint8(x_74, 16);
x_101 = lean_ctor_get_uint8(x_74, 17);
if (lean_is_exclusive(x_74)) {
 x_102 = x_74;
} else {
 lean_dec_ref(x_74);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 0, 18);
} else {
 x_103 = x_102;
}
lean_ctor_set_uint8(x_103, 0, x_85);
lean_ctor_set_uint8(x_103, 1, x_86);
lean_ctor_set_uint8(x_103, 2, x_87);
lean_ctor_set_uint8(x_103, 3, x_88);
lean_ctor_set_uint8(x_103, 4, x_89);
lean_ctor_set_uint8(x_103, 5, x_90);
lean_ctor_set_uint8(x_103, 6, x_91);
lean_ctor_set_uint8(x_103, 7, x_92);
lean_ctor_set_uint8(x_103, 8, x_93);
lean_ctor_set_uint8(x_103, 9, x_12);
lean_ctor_set_uint8(x_103, 10, x_94);
lean_ctor_set_uint8(x_103, 11, x_95);
lean_ctor_set_uint8(x_103, 12, x_96);
lean_ctor_set_uint8(x_103, 13, x_97);
lean_ctor_set_uint8(x_103, 14, x_98);
lean_ctor_set_uint8(x_103, 15, x_99);
lean_ctor_set_uint8(x_103, 16, x_100);
lean_ctor_set_uint8(x_103, 17, x_101);
x_104 = 2;
x_105 = lean_uint64_shift_right(x_75, x_104);
x_106 = lean_uint64_shift_left(x_105, x_104);
x_107 = l_Lean_Meta_TransparencyMode_toUInt64(x_12);
x_108 = lean_uint64_lor(x_106, x_107);
x_109 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_77);
lean_ctor_set(x_109, 2, x_78);
lean_ctor_set(x_109, 3, x_79);
lean_ctor_set(x_109, 4, x_80);
lean_ctor_set(x_109, 5, x_81);
lean_ctor_set(x_109, 6, x_82);
lean_ctor_set_uint64(x_109, sizeof(void*)*7, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 8, x_76);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 9, x_83);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 10, x_84);
x_110 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_9, x_11, x_109, x_4, x_5, x_6, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_10);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_2);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_10);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_10);
lean_dec(x_2);
x_119 = lean_ctor_get(x_110, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_110, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; 
x_8 = lean_st_ref_get(x_6, x_7);
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
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_13);
x_18 = l_Lean_getStructureInfo_x3f(x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_2);
x_14 = x_10;
goto block_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_StructureInfo_getProjFn_x3f(x_19, x_4);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_2);
x_14 = x_10;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_const___override(x_21, x_2);
x_23 = l_Lean_mkAppN(x_22, x_3);
x_24 = l_Lean_Expr_app___override(x_23, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_proj___override(x_13, x_4, x_5);
if (lean_is_scalar(x_11)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_11;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkProjFn___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkProjFn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkProjFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a constructor", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 6)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1;
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_MessageData_ofConstName(x_1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_22, x_2, x_3, x_4, x_5, x_15);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_nat_dec_lt(x_7, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Meta_mkProjFn___redArg(x_1, x_2, x_3, x_7, x_4, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_app___override(x_6, x_15);
x_18 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_6 = x_17;
x_7 = x_18;
x_9 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_Meta_useEtaStruct___redArg(x_1, x_3, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = l_Lean_isStructureLike(x_20, x_1);
if (x_21 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_22; 
lean_free_object(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_whnf(x_26, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_29, x_4, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Expr_getAppFn(x_33);
x_36 = l_Lean_Expr_isConstOf(x_35, x_1);
lean_dec(x_1);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
if (lean_obj_tag(x_35) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_31);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_39 = lean_infer_type(x_33, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_whnfD(x_40, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_47 = lean_expr_eqv(x_44, x_46);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_42);
x_48 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_37, x_6, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
lean_inc(x_55);
x_56 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(x_55, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 4);
lean_inc(x_60);
x_61 = l_Lean_Expr_getAppNumArgs(x_33);
lean_inc(x_61);
x_62 = lean_mk_array(x_61, x_46);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_61, x_63);
lean_dec(x_61);
x_65 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_62, x_64);
x_66 = l_Array_shrink___redArg(x_65, x_59);
lean_dec(x_59);
lean_inc(x_38);
x_67 = l_Lean_Expr_const___override(x_55, x_38);
x_68 = l_Lean_mkAppN(x_67, x_66);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_63);
x_71 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_57, x_38, x_66, x_2, x_70, x_68, x_69, x_6, x_58);
lean_dec(x_6);
lean_dec(x_70);
lean_dec(x_66);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_55);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_56);
if (x_72 == 0)
{
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_56, 0);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_56);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_42, 0, x_2);
return x_42;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_42, 0);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_42);
x_78 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_79 = lean_expr_eqv(x_76, x_78);
lean_dec(x_76);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_37, x_6, x_77);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
lean_inc(x_86);
x_87 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(x_86, x_3, x_4, x_5, x_6, x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 4);
lean_inc(x_91);
x_92 = l_Lean_Expr_getAppNumArgs(x_33);
lean_inc(x_92);
x_93 = lean_mk_array(x_92, x_78);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_92, x_94);
lean_dec(x_92);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_93, x_95);
x_97 = l_Array_shrink___redArg(x_96, x_90);
lean_dec(x_90);
lean_inc(x_38);
x_98 = l_Lean_Expr_const___override(x_86, x_38);
x_99 = l_Lean_mkAppN(x_98, x_97);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_94);
x_102 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_88, x_38, x_97, x_2, x_101, x_99, x_100, x_6, x_89);
lean_dec(x_6);
lean_dec(x_101);
lean_dec(x_97);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_86);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_2);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_105 = x_87;
} else {
 lean_dec_ref(x_87);
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
}
else
{
lean_object* x_107; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_2);
lean_ctor_set(x_107, 1, x_77);
return x_107;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_42;
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_31, 0);
x_109 = lean_ctor_get(x_31, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_31);
x_110 = l_Lean_Expr_getAppFn(x_108);
x_111 = l_Lean_Expr_isConstOf(x_110, x_1);
lean_dec(x_1);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
if (lean_obj_tag(x_110) == 4)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_108);
x_115 = lean_infer_type(x_108, x_3, x_4, x_5, x_6, x_109);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_118 = l_Lean_Meta_whnfD(x_116, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_123 = lean_expr_eqv(x_119, x_122);
lean_dec(x_119);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_121);
x_124 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_113, x_6, x_120);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_114);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_2);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
lean_inc(x_130);
x_131 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(x_130, x_3, x_4, x_5, x_6, x_129);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 4);
lean_inc(x_135);
x_136 = l_Lean_Expr_getAppNumArgs(x_108);
lean_inc(x_136);
x_137 = lean_mk_array(x_136, x_122);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_sub(x_136, x_138);
lean_dec(x_136);
x_140 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_108, x_137, x_139);
x_141 = l_Array_shrink___redArg(x_140, x_134);
lean_dec(x_134);
lean_inc(x_114);
x_142 = l_Lean_Expr_const___override(x_130, x_114);
x_143 = l_Lean_mkAppN(x_142, x_141);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_135);
lean_ctor_set(x_145, 2, x_138);
x_146 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_132, x_114, x_141, x_2, x_145, x_143, x_144, x_6, x_133);
lean_dec(x_6);
lean_dec(x_145);
lean_dec(x_141);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_130);
lean_dec(x_114);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_2);
x_147 = lean_ctor_get(x_131, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_131, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_149 = x_131;
} else {
 lean_dec_ref(x_131);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_121)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_121;
}
lean_ctor_set(x_151, 0, x_2);
lean_ctor_set(x_151, 1, x_120);
return x_151;
}
}
else
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_118;
}
}
else
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_115;
}
}
else
{
lean_object* x_152; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_2);
lean_ctor_set(x_152, 1, x_109);
return x_152;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
else
{
uint8_t x_153; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_22);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_22, 0);
lean_dec(x_154);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_22, 1);
lean_inc(x_155);
lean_dec(x_22);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_22);
if (x_157 == 0)
{
return x_22;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_22, 0);
x_159 = lean_ctor_get(x_22, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_22);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_16, 0);
x_162 = lean_ctor_get(x_16, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_16);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_1);
x_164 = l_Lean_isStructureLike(x_163, x_1);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_166 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_172 = lean_whnf(x_170, x_3, x_4, x_5, x_6, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_173, x_4, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = l_Lean_Expr_getAppFn(x_176);
x_180 = l_Lean_Expr_isConstOf(x_179, x_1);
lean_dec(x_1);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_2);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
if (lean_obj_tag(x_179) == 4)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_dec(x_179);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_176);
x_184 = lean_infer_type(x_176, x_3, x_4, x_5, x_6, x_177);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_187 = l_Lean_Meta_whnfD(x_185, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_192 = lean_expr_eqv(x_188, x_191);
lean_dec(x_188);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_190);
x_193 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___redArg(x_182, x_6, x_189);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_183);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_dec(x_193);
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
lean_inc(x_199);
x_200 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(x_199, x_3, x_4, x_5, x_6, x_198);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 4);
lean_inc(x_204);
x_205 = l_Lean_Expr_getAppNumArgs(x_176);
lean_inc(x_205);
x_206 = lean_mk_array(x_205, x_191);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_sub(x_205, x_207);
lean_dec(x_205);
x_209 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_176, x_206, x_208);
x_210 = l_Array_shrink___redArg(x_209, x_203);
lean_dec(x_203);
lean_inc(x_183);
x_211 = l_Lean_Expr_const___override(x_199, x_183);
x_212 = l_Lean_mkAppN(x_211, x_210);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_204);
lean_ctor_set(x_214, 2, x_207);
x_215 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_201, x_183, x_210, x_2, x_214, x_212, x_213, x_6, x_202);
lean_dec(x_6);
lean_dec(x_214);
lean_dec(x_210);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_199);
lean_dec(x_183);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_2);
x_216 = lean_ctor_get(x_200, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_200, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_218 = x_200;
} else {
 lean_dec_ref(x_200);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_190)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_190;
}
lean_ctor_set(x_220, 0, x_2);
lean_ctor_set(x_220, 1, x_189);
return x_220;
}
}
else
{
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_187;
}
}
else
{
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_184;
}
}
else
{
lean_object* x_221; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_178)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_178;
}
lean_ctor_set(x_221, 0, x_2);
lean_ctor_set(x_221, 1, x_177);
return x_221;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_172;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_169;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_167);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_166, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_223 = x_166;
} else {
 lean_dec_ref(x_166);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_2);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_ctor_get(x_166, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_166, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_227 = x_166;
} else {
 lean_dec_ref(x_166);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Acc", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WellFounded", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4;
x_5 = lean_name_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cleanupNatOffsetMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_23 = l_Lean_mkNatLit(x_22);
x_24 = l_Lean_mkNatAdd(x_16, x_23);
x_25 = l_Lean_mkNatSucc(x_24);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; 
lean_dec(x_17);
x_26 = l_Lean_mkNatSucc(x_16);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_dec(x_17);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_29, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_35 = l_Lean_mkNatLit(x_34);
x_36 = l_Lean_mkNatAdd(x_28, x_35);
x_37 = l_Lean_mkNatSucc(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_39 = l_Lean_mkNatSucc(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_27);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_27);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_RecursorVal_getMajorIdx(x_1);
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_4, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_91; uint8_t x_92; uint8_t x_163; 
x_16 = l_Lean_Meta_getTransparency___redArg(x_6, x_10);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 5);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_91 = lean_array_fget(x_3, x_11);
x_163 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec(x_24);
lean_dec(x_24);
if (x_163 == 0)
{
lean_dec(x_18);
x_92 = x_163;
goto block_162;
}
else
{
lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; 
x_164 = lean_box(1);
x_165 = lean_unbox(x_18);
lean_dec(x_18);
x_166 = lean_unbox(x_164);
x_167 = l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_165, x_166);
x_92 = x_167;
goto block_162;
}
block_76:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_toCtorIfLit(x_26);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_33 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cleanupNatOffsetMajor(x_32, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_RecursorVal_getMajorInduct(x_1);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_37 = l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure(x_36, x_34, x_27, x_28, x_29, x_30, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(x_1, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_apply_6(x_4, x_41, x_27, x_28, x_29, x_30, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_List_lengthTR___redArg(x_2);
x_45 = l_List_lengthTR___redArg(x_25);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_apply_6(x_4, x_47, x_27, x_28, x_29, x_30, x_39);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 2);
lean_inc(x_50);
lean_dec(x_43);
x_51 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_52 = l_Lean_Expr_getAppNumArgs(x_38);
lean_inc(x_52);
x_53 = lean_mk_array(x_52, x_51);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_52, x_54);
lean_dec(x_52);
x_56 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_38, x_53, x_55);
x_57 = l_Lean_Expr_instantiateLevelParams(x_50, x_25, x_2);
lean_dec(x_50);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_add(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_60 = lean_nat_add(x_59, x_22);
lean_dec(x_22);
lean_dec(x_59);
x_61 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_60, x_3, x_58, x_57);
lean_dec(x_60);
x_62 = lean_array_get_size(x_56);
x_63 = lean_nat_sub(x_62, x_49);
lean_dec(x_49);
x_64 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_62, x_56, x_63, x_61);
lean_dec(x_56);
lean_dec(x_62);
x_65 = lean_nat_add(x_11, x_54);
lean_dec(x_11);
x_66 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_12, x_3, x_65, x_64);
lean_dec(x_12);
x_67 = lean_apply_6(x_5, x_66, x_27, x_28, x_29, x_30, x_39);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_33);
if (x_72 == 0)
{
return x_33;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_33, 0);
x_74 = lean_ctor_get(x_33, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_33);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
block_90:
{
if (x_23 == 0)
{
x_26 = x_77;
x_27 = x_78;
x_28 = x_79;
x_29 = x_80;
x_30 = x_81;
x_31 = x_82;
goto block_76;
}
else
{
lean_object* x_83; 
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_1);
x_83 = l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(x_1, x_77, x_78, x_79, x_80, x_81, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_26 = x_84;
x_27 = x_78;
x_28 = x_79;
x_29 = x_80;
x_30 = x_81;
x_31 = x_85;
goto block_76;
}
else
{
uint8_t x_86; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
block_162:
{
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = lean_whnf(x_91, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_77 = x_94;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_95;
goto block_90;
}
else
{
uint8_t x_96; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_93);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; uint64_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_100 = lean_ctor_get(x_6, 0);
lean_inc(x_100);
x_101 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_102 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_6, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_6, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_6, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_6, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_6, 6);
lean_inc(x_108);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
uint8_t x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_111 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
lean_ctor_set_uint8(x_100, 9, x_113);
x_114 = 2;
x_115 = lean_uint64_shift_right(x_101, x_114);
x_116 = lean_uint64_shift_left(x_115, x_114);
x_117 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0;
x_118 = lean_uint64_lor(x_116, x_117);
x_119 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_119, 0, x_100);
lean_ctor_set(x_119, 1, x_103);
lean_ctor_set(x_119, 2, x_104);
lean_ctor_set(x_119, 3, x_105);
lean_ctor_set(x_119, 4, x_106);
lean_ctor_set(x_119, 5, x_107);
lean_ctor_set(x_119, 6, x_108);
lean_ctor_set_uint64(x_119, sizeof(void*)*7, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 8, x_102);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 9, x_110);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 10, x_111);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_120 = lean_whnf(x_91, x_119, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_77 = x_121;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_122;
goto block_90;
}
else
{
uint8_t x_123; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_120);
if (x_123 == 0)
{
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 0);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_120);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; lean_object* x_154; lean_object* x_155; 
x_127 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_128 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_129 = lean_ctor_get_uint8(x_100, 0);
x_130 = lean_ctor_get_uint8(x_100, 1);
x_131 = lean_ctor_get_uint8(x_100, 2);
x_132 = lean_ctor_get_uint8(x_100, 3);
x_133 = lean_ctor_get_uint8(x_100, 4);
x_134 = lean_ctor_get_uint8(x_100, 5);
x_135 = lean_ctor_get_uint8(x_100, 6);
x_136 = lean_ctor_get_uint8(x_100, 7);
x_137 = lean_ctor_get_uint8(x_100, 8);
x_138 = lean_ctor_get_uint8(x_100, 10);
x_139 = lean_ctor_get_uint8(x_100, 11);
x_140 = lean_ctor_get_uint8(x_100, 12);
x_141 = lean_ctor_get_uint8(x_100, 13);
x_142 = lean_ctor_get_uint8(x_100, 14);
x_143 = lean_ctor_get_uint8(x_100, 15);
x_144 = lean_ctor_get_uint8(x_100, 16);
x_145 = lean_ctor_get_uint8(x_100, 17);
lean_dec(x_100);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_147, 0, x_129);
lean_ctor_set_uint8(x_147, 1, x_130);
lean_ctor_set_uint8(x_147, 2, x_131);
lean_ctor_set_uint8(x_147, 3, x_132);
lean_ctor_set_uint8(x_147, 4, x_133);
lean_ctor_set_uint8(x_147, 5, x_134);
lean_ctor_set_uint8(x_147, 6, x_135);
lean_ctor_set_uint8(x_147, 7, x_136);
lean_ctor_set_uint8(x_147, 8, x_137);
x_148 = lean_unbox(x_146);
lean_ctor_set_uint8(x_147, 9, x_148);
lean_ctor_set_uint8(x_147, 10, x_138);
lean_ctor_set_uint8(x_147, 11, x_139);
lean_ctor_set_uint8(x_147, 12, x_140);
lean_ctor_set_uint8(x_147, 13, x_141);
lean_ctor_set_uint8(x_147, 14, x_142);
lean_ctor_set_uint8(x_147, 15, x_143);
lean_ctor_set_uint8(x_147, 16, x_144);
lean_ctor_set_uint8(x_147, 17, x_145);
x_149 = 2;
x_150 = lean_uint64_shift_right(x_101, x_149);
x_151 = lean_uint64_shift_left(x_150, x_149);
x_152 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0;
x_153 = lean_uint64_lor(x_151, x_152);
x_154 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_103);
lean_ctor_set(x_154, 2, x_104);
lean_ctor_set(x_154, 3, x_105);
lean_ctor_set(x_154, 4, x_106);
lean_ctor_set(x_154, 5, x_107);
lean_ctor_set(x_154, 6, x_108);
lean_ctor_set_uint64(x_154, sizeof(void*)*7, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 8, x_102);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 9, x_127);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 10, x_128);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_155 = lean_whnf(x_91, x_154, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_77 = x_156;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_157;
goto block_90;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_73; lean_object* x_74; 
x_73 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_74 = lean_box(x_73);
switch (lean_obj_tag(x_74)) {
case 2:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_unsigned_to_nat(5u);
x_76 = lean_unsigned_to_nat(3u);
x_26 = x_75;
x_27 = x_76;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
goto block_72;
}
case 3:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_unsigned_to_nat(3u);
x_26 = x_77;
x_27 = x_78;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
goto block_72;
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_4);
x_79 = lean_box(0);
x_80 = lean_apply_6(x_3, x_79, x_5, x_6, x_7, x_8, x_9);
return x_80;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_6(x_3, x_15, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_apply_6(x_3, x_23, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
block_72:
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_2);
x_34 = lean_nat_dec_lt(x_26, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_4);
x_35 = lean_box(0);
x_36 = lean_apply_6(x_3, x_35, x_28, x_29, x_30, x_31, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_array_fget(x_2, x_26);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_38 = lean_whnf(x_37, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 5)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 5)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_st_ref_get(x_31, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_Environment_find_x3f(x_49, x_45, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_4);
x_18 = x_28;
x_19 = x_29;
x_20 = x_30;
x_21 = x_31;
x_22 = x_48;
goto block_25;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
x_56 = lean_box(x_55);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
x_57 = l_Lean_instInhabitedExpr;
x_58 = lean_array_get(x_57, x_2, x_27);
x_59 = l_Lean_Expr_app___override(x_58, x_44);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_26, x_60);
x_62 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_33, x_2, x_61, x_59);
lean_dec(x_33);
x_63 = lean_apply_6(x_4, x_62, x_28, x_29, x_30, x_31, x_48);
return x_63;
}
else
{
lean_dec(x_56);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_4);
x_18 = x_28;
x_19 = x_29;
x_20 = x_30;
x_21 = x_31;
x_22 = x_48;
goto block_25;
}
}
else
{
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_4);
x_18 = x_28;
x_19 = x_29;
x_20 = x_30;
x_21 = x_31;
x_22 = x_48;
goto block_25;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_4);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_64;
goto block_17;
}
}
else
{
lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_4);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_dec(x_38);
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_65;
goto block_17;
}
}
else
{
lean_object* x_66; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_4);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
lean_dec(x_38);
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_66;
goto block_17;
}
}
else
{
lean_object* x_67; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_4);
x_67 = lean_ctor_get(x_38, 1);
lean_inc(x_67);
lean_dec(x_38);
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_67;
goto block_17;
}
}
else
{
uint8_t x_68; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
return x_38;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_38, 0);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_38);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_RecursorVal_getMajorIdx(x_1);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_whnf(x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_getStuckMVar_x3f(x_16, x_3, x_4, x_5, x_6, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_get_projection_info(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_projection_info(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_20, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_array_uget(x_2, x_4);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_inc(x_22);
lean_ctor_set(x_20, 1, x_33);
x_34 = l_Lean_Meta_ParamInfo_isExplicit(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_11 = x_5;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = l_Lean_Meta_getStuckMVar_x3f(x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_5, 0, x_41);
lean_ctor_set(x_36, 0, x_5);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_5, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_20);
x_49 = lean_array_uget(x_2, x_4);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_23, x_50);
lean_inc(x_22);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_24);
x_53 = l_Lean_Meta_ParamInfo_isExplicit(x_49);
lean_dec(x_49);
if (x_53 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_52);
lean_ctor_set(x_5, 0, x_1);
x_11 = x_5;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Meta_getStuckMVar_x3f(x_54, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_52);
lean_ctor_set(x_5, 0, x_1);
x_11 = x_5;
x_12 = x_57;
goto block_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_5, 1, x_52);
lean_ctor_set(x_5, 0, x_60);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
x_70 = lean_nat_dec_lt(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_10);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
x_74 = lean_array_uget(x_2, x_4);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_68, x_75);
lean_inc(x_67);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 3, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_69);
x_78 = l_Lean_Meta_ParamInfo_isExplicit(x_74);
lean_dec(x_74);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_68);
lean_dec(x_67);
lean_inc(x_1);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_77);
x_11 = x_79;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_array_fget(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = l_Lean_Meta_getStuckMVar_x3f(x_80, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_77);
x_11 = x_84;
x_12 = x_83;
goto block_16;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_92 = x_81;
} else {
 lean_dec_ref(x_81);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 2)
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_1 = x_23;
x_6 = x_32;
goto _start;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = l_Lean_Expr_getAppFn(x_34);
lean_dec(x_34);
switch (lean_obj_tag(x_35)) {
case 2:
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_35);
x_101 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
x_105 = l_Lean_Expr_getAppFn(x_103);
if (lean_obj_tag(x_105) == 2)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_101, 0, x_107);
return x_101;
}
else
{
lean_dec(x_105);
lean_free_object(x_101);
x_1 = x_103;
x_6 = x_104;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_101, 0);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_101);
x_111 = l_Lean_Expr_getAppFn(x_109);
if (lean_obj_tag(x_111) == 2)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_109);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
else
{
lean_dec(x_111);
x_1 = x_109;
x_6 = x_110;
goto _start;
}
}
}
case 4:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_116 = lean_ctor_get(x_35, 0);
lean_inc(x_116);
x_156 = lean_st_ref_get(x_5, x_6);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = lean_unbox(x_160);
lean_inc(x_116);
x_162 = l_Lean_Environment_find_x3f(x_159, x_116, x_161);
if (lean_obj_tag(x_162) == 0)
{
x_117 = x_2;
x_118 = x_3;
x_119 = x_4;
x_120 = x_5;
x_121 = x_158;
goto block_155;
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
switch (lean_obj_tag(x_163)) {
case 4:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_116);
lean_dec(x_35);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_166 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_166);
x_167 = lean_mk_array(x_166, x_165);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_sub(x_166, x_168);
lean_dec(x_166);
x_170 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_167, x_169);
x_171 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_164, x_170, x_2, x_3, x_4, x_5, x_158);
lean_dec(x_170);
lean_dec(x_164);
return x_171;
}
case 7:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_116);
lean_dec(x_35);
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
lean_dec(x_163);
x_173 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_174 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_174);
x_175 = lean_mk_array(x_174, x_173);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_sub(x_174, x_176);
lean_dec(x_174);
x_178 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_175, x_177);
x_179 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_172, x_178, x_2, x_3, x_4, x_5, x_158);
lean_dec(x_178);
lean_dec(x_172);
return x_179;
}
default: 
{
lean_dec(x_163);
x_117 = x_2;
x_118 = x_3;
x_119 = x_4;
x_120 = x_5;
x_121 = x_158;
goto block_155;
}
}
}
block_155:
{
uint8_t x_122; 
x_122 = l_Lean_Expr_hasExprMVar(x_1);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_35);
lean_dec(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(x_116, x_120, x_121);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_35);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 0);
lean_dec(x_128);
x_129 = lean_box(0);
lean_ctor_set(x_125, 0, x_129);
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_126, 0);
lean_inc(x_133);
lean_dec(x_126);
x_134 = lean_ctor_get_uint8(x_133, sizeof(void*)*3);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_133);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_35);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_125);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_125, 0);
lean_dec(x_136);
x_137 = lean_box(0);
lean_ctor_set(x_125, 0, x_137);
return x_125;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_125, 1);
lean_inc(x_138);
lean_dec(x_125);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
lean_dec(x_125);
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
lean_dec(x_133);
x_143 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_144 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_144);
x_145 = lean_mk_array(x_144, x_143);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_sub(x_144, x_146);
lean_dec(x_144);
x_148 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_145, x_147);
x_149 = lean_array_get_size(x_148);
x_150 = lean_nat_dec_lt(x_142, x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_dec(x_142);
x_36 = x_148;
x_37 = x_117;
x_38 = x_118;
x_39 = x_119;
x_40 = x_120;
x_41 = x_141;
goto block_100;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_array_fget(x_148, x_142);
lean_dec(x_142);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
x_152 = l_Lean_Meta_getStuckMVar_x3f(x_151, x_117, x_118, x_119, x_120, x_141);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_36 = x_148;
x_37 = x_117;
x_38 = x_118;
x_39 = x_119;
x_40 = x_120;
x_41 = x_154;
goto block_100;
}
else
{
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_35);
return x_152;
}
}
else
{
lean_dec(x_148);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_35);
return x_152;
}
}
}
}
}
}
}
case 11:
{
lean_object* x_180; 
lean_dec(x_1);
x_180 = lean_ctor_get(x_35, 2);
lean_inc(x_180);
lean_dec(x_35);
x_7 = x_180;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
goto block_21;
}
default: 
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_6);
return x_182;
}
}
block_100:
{
lean_object* x_42; 
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_42 = l_Lean_Meta_getFunInfo(x_35, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_dec(x_47);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get_size(x_36);
x_50 = l_Array_toSubarray___redArg(x_36, x_48, x_49);
x_51 = lean_box(0);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_51);
x_52 = lean_array_size(x_46);
x_53 = 0;
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1(x_51, x_46, x_52, x_53, x_43, x_37, x_38, x_39, x_40, x_44);
lean_dec(x_46);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_54, 0, x_59);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_54, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_65);
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_43, 0);
lean_inc(x_73);
lean_dec(x_43);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_36);
x_76 = l_Array_toSubarray___redArg(x_36, x_74, x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_array_size(x_73);
x_80 = 0;
x_81 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1(x_77, x_73, x_79, x_80, x_78, x_37, x_38, x_39, x_40, x_44);
lean_dec(x_73);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
lean_dec(x_83);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_96 = !lean_is_exclusive(x_42);
if (x_96 == 0)
{
return x_42;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_42, 0);
x_98 = lean_ctor_get(x_42, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_42);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
case 10:
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_1, 1);
lean_inc(x_183);
lean_dec(x_1);
x_1 = x_183;
goto _start;
}
case 11:
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_1, 2);
lean_inc(x_185);
lean_dec(x_1);
x_7 = x_185;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
goto block_21;
}
default: 
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_6);
return x_187;
}
}
block_21:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_whnf(x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_14;
x_2 = x_8;
x_3 = x_9;
x_4 = x_10;
x_5 = x_11;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_28; lean_object* x_29; 
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_29 = lean_box(x_28);
switch (lean_obj_tag(x_29)) {
case 2:
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(5u);
x_8 = x_30;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_27;
}
case 3:
{
lean_object* x_31; 
x_31 = lean_unsigned_to_nat(4u);
x_8 = x_31;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_27;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
return x_33;
}
}
block_27:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_2, x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = lean_whnf(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_getStuckMVar_x3f(x_20, x_9, x_10, x_11, x_12, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getStuckMVar_x3f_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_whnfEasyCases___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_quickCmp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.WHNF", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.whnfEasyCases", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("loose bvar in expression", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__9;
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_unsigned_to_nat(366u);
x_4 = l_Lean_Meta_whnfEasyCases___closed__8;
x_5 = l_Lean_Meta_whnfEasyCases___closed__7;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_whnfEasyCases___closed__1;
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_Lean_Meta_whnfEasyCases___closed__2;
x_19 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = l_Lean_Meta_whnfEasyCases___closed__4;
x_37 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
x_44 = l_Lean_Meta_instMonadMCtxMetaM;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l_Lean_Meta_whnfEasyCases___closed__6;
x_46 = l_Lean_Meta_whnfEasyCases___closed__10;
x_47 = l_panic___redArg(x_45, x_46);
x_48 = lean_apply_5(x_47, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
case 1:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_26);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_inc(x_3);
lean_inc(x_49);
x_50 = l_Lean_FVarId_getDecl___redArg(x_49, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
lean_ctor_set(x_50, 0, x_1);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 4);
lean_inc(x_57);
x_58 = l_Lean_Meta_getConfig___redArg(x_3, x_56);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_94; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_94 = l_Lean_LocalDecl_isImplementationDetail(x_51);
lean_dec(x_51);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_60, 16);
lean_dec(x_60);
if (x_95 == 0)
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
x_98 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_49);
x_99 = l_Lean_RBNode_findCore___redArg(x_98, x_97, x_49);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
else
{
lean_dec(x_99);
lean_free_object(x_58);
lean_dec(x_1);
x_62 = x_3;
x_63 = x_96;
x_64 = x_4;
x_65 = x_5;
x_66 = x_6;
goto block_87;
}
}
else
{
lean_free_object(x_58);
lean_dec(x_1);
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
goto block_93;
}
}
else
{
lean_free_object(x_58);
lean_dec(x_60);
lean_dec(x_1);
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
goto block_93;
}
block_87:
{
if (x_63 == 0)
{
lean_dec(x_49);
x_1 = x_57;
x_3 = x_62;
x_4 = x_64;
x_5 = x_65;
x_6 = x_66;
x_7 = x_61;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_st_ref_take(x_64, x_61);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_69, 2);
x_73 = l_Lean_FVarIdSet_insert(x_72, x_49);
lean_ctor_set(x_69, 2, x_73);
x_74 = lean_st_ref_set(x_64, x_69, x_70);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_1 = x_57;
x_3 = x_62;
x_4 = x_64;
x_5 = x_65;
x_6 = x_66;
x_7 = x_75;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_69, 0);
x_78 = lean_ctor_get(x_69, 1);
x_79 = lean_ctor_get(x_69, 2);
x_80 = lean_ctor_get(x_69, 3);
x_81 = lean_ctor_get(x_69, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_69);
x_82 = l_Lean_FVarIdSet_insert(x_79, x_49);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_80);
lean_ctor_set(x_83, 4, x_81);
x_84 = lean_st_ref_set(x_64, x_83, x_70);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_1 = x_57;
x_3 = x_62;
x_4 = x_64;
x_5 = x_65;
x_6 = x_66;
x_7 = x_85;
goto _start;
}
}
}
block_93:
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_88, sizeof(void*)*7 + 8);
x_62 = x_88;
x_63 = x_92;
x_64 = x_89;
x_65 = x_90;
x_66 = x_91;
goto block_87;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_129; 
x_100 = lean_ctor_get(x_58, 0);
x_101 = lean_ctor_get(x_58, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_58);
x_129 = l_Lean_LocalDecl_isImplementationDetail(x_51);
lean_dec(x_51);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_100, 16);
lean_dec(x_100);
if (x_130 == 0)
{
uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_49);
x_134 = l_Lean_RBNode_findCore___redArg(x_133, x_132, x_49);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_101);
return x_135;
}
else
{
lean_dec(x_134);
lean_dec(x_1);
x_102 = x_3;
x_103 = x_131;
x_104 = x_4;
x_105 = x_5;
x_106 = x_6;
goto block_122;
}
}
else
{
lean_dec(x_1);
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
goto block_128;
}
}
else
{
lean_dec(x_100);
lean_dec(x_1);
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
goto block_128;
}
block_122:
{
if (x_103 == 0)
{
lean_dec(x_49);
x_1 = x_57;
x_3 = x_102;
x_4 = x_104;
x_5 = x_105;
x_6 = x_106;
x_7 = x_101;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_108 = lean_st_ref_take(x_104, x_101);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
x_117 = l_Lean_FVarIdSet_insert(x_113, x_49);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_111);
lean_ctor_set(x_118, 1, x_112);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_115);
x_119 = lean_st_ref_set(x_104, x_118, x_110);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_1 = x_57;
x_3 = x_102;
x_4 = x_104;
x_5 = x_105;
x_6 = x_106;
x_7 = x_120;
goto _start;
}
}
block_128:
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_123, sizeof(void*)*7 + 8);
x_102 = x_123;
x_103 = x_127;
x_104 = x_124;
x_105 = x_125;
x_106 = x_126;
goto block_122;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_50);
if (x_136 == 0)
{
return x_50;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_50, 0);
x_138 = lean_ctor_get(x_50, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_50);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
case 2:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_1, 0);
lean_inc(x_140);
x_141 = l_Lean_getExprMVarAssignment_x3f___redArg(x_26, x_44, x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_142 = lean_apply_5(x_141, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_142);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_142, 0);
lean_dec(x_145);
lean_ctor_set(x_142, 0, x_1);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_1);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
lean_dec(x_143);
x_1 = x_149;
x_7 = x_148;
goto _start;
}
}
else
{
uint8_t x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_142);
if (x_151 == 0)
{
return x_142;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_142, 0);
x_153 = lean_ctor_get(x_142, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_142);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
case 3:
{
lean_object* x_155; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_7);
return x_155;
}
case 6:
{
lean_object* x_156; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_7);
return x_156;
}
case 7:
{
lean_object* x_157; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_7);
return x_157;
}
case 9:
{
lean_object* x_158; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_7);
return x_158;
}
case 10:
{
lean_object* x_159; 
lean_dec(x_26);
x_159 = lean_ctor_get(x_1, 1);
lean_inc(x_159);
lean_dec(x_1);
x_1 = x_159;
goto _start;
}
default: 
{
lean_object* x_161; 
lean_dec(x_26);
x_161 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_162 = lean_ctor_get(x_28, 0);
x_163 = lean_ctor_get(x_28, 2);
x_164 = lean_ctor_get(x_28, 3);
x_165 = lean_ctor_get(x_28, 4);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_28);
x_166 = l_Lean_Meta_whnfEasyCases___closed__4;
x_167 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_162);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_168, 0, x_162);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_169, 0, x_162);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_171, 0, x_165);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_172, 0, x_164);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_173, 0, x_163);
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set(x_174, 1, x_166);
lean_ctor_set(x_174, 2, x_173);
lean_ctor_set(x_174, 3, x_172);
lean_ctor_set(x_174, 4, x_171);
lean_ctor_set(x_26, 1, x_167);
lean_ctor_set(x_26, 0, x_174);
x_175 = l_Lean_Meta_instMonadMCtxMetaM;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_176 = l_Lean_Meta_whnfEasyCases___closed__6;
x_177 = l_Lean_Meta_whnfEasyCases___closed__10;
x_178 = l_panic___redArg(x_176, x_177);
x_179 = lean_apply_5(x_178, x_3, x_4, x_5, x_6, x_7);
return x_179;
}
case 1:
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_26);
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
lean_inc(x_3);
lean_inc(x_180);
x_181 = l_Lean_FVarId_getDecl___redArg(x_180, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_1);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_219; 
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_ctor_get(x_182, 4);
lean_inc(x_187);
x_188 = l_Lean_Meta_getConfig___redArg(x_3, x_186);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_219 = l_Lean_LocalDecl_isImplementationDetail(x_182);
lean_dec(x_182);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = lean_ctor_get_uint8(x_189, 16);
lean_dec(x_189);
if (x_220 == 0)
{
uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_222 = lean_ctor_get(x_3, 1);
lean_inc(x_222);
x_223 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_180);
x_224 = l_Lean_RBNode_findCore___redArg(x_223, x_222, x_180);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; 
lean_dec(x_187);
lean_dec(x_180);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_191)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_191;
}
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_190);
return x_225;
}
else
{
lean_dec(x_224);
lean_dec(x_191);
lean_dec(x_1);
x_192 = x_3;
x_193 = x_221;
x_194 = x_4;
x_195 = x_5;
x_196 = x_6;
goto block_212;
}
}
else
{
lean_dec(x_191);
lean_dec(x_1);
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
goto block_218;
}
}
else
{
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_1);
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
goto block_218;
}
block_212:
{
if (x_193 == 0)
{
lean_dec(x_180);
x_1 = x_187;
x_3 = x_192;
x_4 = x_194;
x_5 = x_195;
x_6 = x_196;
x_7 = x_190;
goto _start;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_198 = lean_st_ref_take(x_194, x_190);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 4);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
x_207 = l_Lean_FVarIdSet_insert(x_203, x_180);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_201);
lean_ctor_set(x_208, 1, x_202);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_208, 3, x_204);
lean_ctor_set(x_208, 4, x_205);
x_209 = lean_st_ref_set(x_194, x_208, x_200);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_1 = x_187;
x_3 = x_192;
x_4 = x_194;
x_5 = x_195;
x_6 = x_196;
x_7 = x_210;
goto _start;
}
}
block_218:
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_213, sizeof(void*)*7 + 8);
x_192 = x_213;
x_193 = x_217;
x_194 = x_214;
x_195 = x_215;
x_196 = x_216;
goto block_212;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_180);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_ctor_get(x_181, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_181, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_228 = x_181;
} else {
 lean_dec_ref(x_181);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
case 2:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_1, 0);
lean_inc(x_230);
x_231 = l_Lean_getExprMVarAssignment_x3f___redArg(x_26, x_175, x_230);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_232 = lean_apply_5(x_231, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_1);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_1);
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_ctor_get(x_233, 0);
lean_inc(x_238);
lean_dec(x_233);
x_1 = x_238;
x_7 = x_237;
goto _start;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_232, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_242 = x_232;
} else {
 lean_dec_ref(x_232);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
case 3:
{
lean_object* x_244; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_1);
lean_ctor_set(x_244, 1, x_7);
return x_244;
}
case 6:
{
lean_object* x_245; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_1);
lean_ctor_set(x_245, 1, x_7);
return x_245;
}
case 7:
{
lean_object* x_246; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_1);
lean_ctor_set(x_246, 1, x_7);
return x_246;
}
case 9:
{
lean_object* x_247; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_1);
lean_ctor_set(x_247, 1, x_7);
return x_247;
}
case 10:
{
lean_object* x_248; 
lean_dec(x_26);
x_248 = lean_ctor_get(x_1, 1);
lean_inc(x_248);
lean_dec(x_1);
x_1 = x_248;
goto _start;
}
default: 
{
lean_object* x_250; 
lean_dec(x_26);
x_250 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_250;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_251 = lean_ctor_get(x_26, 0);
lean_inc(x_251);
lean_dec(x_26);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_251, 4);
lean_inc(x_255);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_256 = x_251;
} else {
 lean_dec_ref(x_251);
 x_256 = lean_box(0);
}
x_257 = l_Lean_Meta_whnfEasyCases___closed__4;
x_258 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_252);
x_259 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_259, 0, x_252);
x_260 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_260, 0, x_252);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_262, 0, x_255);
x_263 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_263, 0, x_254);
x_264 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_264, 0, x_253);
if (lean_is_scalar(x_256)) {
 x_265 = lean_alloc_ctor(0, 5, 0);
} else {
 x_265 = x_256;
}
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_257);
lean_ctor_set(x_265, 2, x_264);
lean_ctor_set(x_265, 3, x_263);
lean_ctor_set(x_265, 4, x_262);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_258);
x_267 = l_Lean_Meta_instMonadMCtxMetaM;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_266);
lean_dec(x_2);
lean_dec(x_1);
x_268 = l_Lean_Meta_whnfEasyCases___closed__6;
x_269 = l_Lean_Meta_whnfEasyCases___closed__10;
x_270 = l_panic___redArg(x_268, x_269);
x_271 = lean_apply_5(x_270, x_3, x_4, x_5, x_6, x_7);
return x_271;
}
case 1:
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_266);
x_272 = lean_ctor_get(x_1, 0);
lean_inc(x_272);
lean_inc(x_3);
lean_inc(x_272);
x_273 = l_Lean_FVarId_getDecl___redArg(x_272, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_311; 
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
lean_dec(x_273);
x_279 = lean_ctor_get(x_274, 4);
lean_inc(x_279);
x_280 = l_Lean_Meta_getConfig___redArg(x_3, x_278);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
x_311 = l_Lean_LocalDecl_isImplementationDetail(x_274);
lean_dec(x_274);
if (x_311 == 0)
{
uint8_t x_312; 
x_312 = lean_ctor_get_uint8(x_281, 16);
lean_dec(x_281);
if (x_312 == 0)
{
uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_314 = lean_ctor_get(x_3, 1);
lean_inc(x_314);
x_315 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_272);
x_316 = l_Lean_RBNode_findCore___redArg(x_315, x_314, x_272);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
lean_dec(x_279);
lean_dec(x_272);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_283)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_283;
}
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_282);
return x_317;
}
else
{
lean_dec(x_316);
lean_dec(x_283);
lean_dec(x_1);
x_284 = x_3;
x_285 = x_313;
x_286 = x_4;
x_287 = x_5;
x_288 = x_6;
goto block_304;
}
}
else
{
lean_dec(x_283);
lean_dec(x_1);
x_305 = x_3;
x_306 = x_4;
x_307 = x_5;
x_308 = x_6;
goto block_310;
}
}
else
{
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_1);
x_305 = x_3;
x_306 = x_4;
x_307 = x_5;
x_308 = x_6;
goto block_310;
}
block_304:
{
if (x_285 == 0)
{
lean_dec(x_272);
x_1 = x_279;
x_3 = x_284;
x_4 = x_286;
x_5 = x_287;
x_6 = x_288;
x_7 = x_282;
goto _start;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_290 = lean_st_ref_take(x_286, x_282);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_291, 3);
lean_inc(x_296);
x_297 = lean_ctor_get(x_291, 4);
lean_inc(x_297);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 lean_ctor_release(x_291, 4);
 x_298 = x_291;
} else {
 lean_dec_ref(x_291);
 x_298 = lean_box(0);
}
x_299 = l_Lean_FVarIdSet_insert(x_295, x_272);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_294);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_300, 3, x_296);
lean_ctor_set(x_300, 4, x_297);
x_301 = lean_st_ref_set(x_286, x_300, x_292);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
x_1 = x_279;
x_3 = x_284;
x_4 = x_286;
x_5 = x_287;
x_6 = x_288;
x_7 = x_302;
goto _start;
}
}
block_310:
{
uint8_t x_309; 
x_309 = lean_ctor_get_uint8(x_305, sizeof(void*)*7 + 8);
x_284 = x_305;
x_285 = x_309;
x_286 = x_306;
x_287 = x_307;
x_288 = x_308;
goto block_304;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_272);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = lean_ctor_get(x_273, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_273, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_320 = x_273;
} else {
 lean_dec_ref(x_273);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
case 2:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_1, 0);
lean_inc(x_322);
x_323 = l_Lean_getExprMVarAssignment_x3f___redArg(x_266, x_267, x_322);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_324 = lean_apply_5(x_323, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_1);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_1);
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_dec(x_324);
x_330 = lean_ctor_get(x_325, 0);
lean_inc(x_330);
lean_dec(x_325);
x_1 = x_330;
x_7 = x_329;
goto _start;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_332 = lean_ctor_get(x_324, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_324, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_334 = x_324;
} else {
 lean_dec_ref(x_324);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
case 3:
{
lean_object* x_336; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_1);
lean_ctor_set(x_336, 1, x_7);
return x_336;
}
case 6:
{
lean_object* x_337; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_1);
lean_ctor_set(x_337, 1, x_7);
return x_337;
}
case 7:
{
lean_object* x_338; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_1);
lean_ctor_set(x_338, 1, x_7);
return x_338;
}
case 9:
{
lean_object* x_339; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_1);
lean_ctor_set(x_339, 1, x_7);
return x_339;
}
case 10:
{
lean_object* x_340; 
lean_dec(x_266);
x_340 = lean_ctor_get(x_1, 1);
lean_inc(x_340);
lean_dec(x_1);
x_1 = x_340;
goto _start;
}
default: 
{
lean_object* x_342; 
lean_dec(x_266);
x_342 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_342;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_343 = lean_ctor_get(x_10, 0);
x_344 = lean_ctor_get(x_10, 2);
x_345 = lean_ctor_get(x_10, 3);
x_346 = lean_ctor_get(x_10, 4);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_10);
x_347 = l_Lean_Meta_whnfEasyCases___closed__2;
x_348 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_343);
x_349 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_349, 0, x_343);
x_350 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_350, 0, x_343);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_352, 0, x_346);
x_353 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_353, 0, x_345);
x_354 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_354, 0, x_344);
x_355 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_347);
lean_ctor_set(x_355, 2, x_354);
lean_ctor_set(x_355, 3, x_353);
lean_ctor_set(x_355, 4, x_352);
lean_ctor_set(x_8, 1, x_348);
lean_ctor_set(x_8, 0, x_355);
x_356 = l_ReaderT_instMonad___redArg(x_8);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_358 = x_356;
} else {
 lean_dec_ref(x_356);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_357, 2);
lean_inc(x_360);
x_361 = lean_ctor_get(x_357, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_357, 4);
lean_inc(x_362);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 x_363 = x_357;
} else {
 lean_dec_ref(x_357);
 x_363 = lean_box(0);
}
x_364 = l_Lean_Meta_whnfEasyCases___closed__4;
x_365 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_359);
x_366 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_366, 0, x_359);
x_367 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_367, 0, x_359);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_369, 0, x_362);
x_370 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_370, 0, x_361);
x_371 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_371, 0, x_360);
if (lean_is_scalar(x_363)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_363;
}
lean_ctor_set(x_372, 0, x_368);
lean_ctor_set(x_372, 1, x_364);
lean_ctor_set(x_372, 2, x_371);
lean_ctor_set(x_372, 3, x_370);
lean_ctor_set(x_372, 4, x_369);
if (lean_is_scalar(x_358)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_358;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_365);
x_374 = l_Lean_Meta_instMonadMCtxMetaM;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_373);
lean_dec(x_2);
lean_dec(x_1);
x_375 = l_Lean_Meta_whnfEasyCases___closed__6;
x_376 = l_Lean_Meta_whnfEasyCases___closed__10;
x_377 = l_panic___redArg(x_375, x_376);
x_378 = lean_apply_5(x_377, x_3, x_4, x_5, x_6, x_7);
return x_378;
}
case 1:
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_373);
x_379 = lean_ctor_get(x_1, 0);
lean_inc(x_379);
lean_inc(x_3);
lean_inc(x_379);
x_380 = l_Lean_FVarId_getDecl___redArg(x_379, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_1);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_418; 
x_385 = lean_ctor_get(x_380, 1);
lean_inc(x_385);
lean_dec(x_380);
x_386 = lean_ctor_get(x_381, 4);
lean_inc(x_386);
x_387 = l_Lean_Meta_getConfig___redArg(x_3, x_385);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
x_418 = l_Lean_LocalDecl_isImplementationDetail(x_381);
lean_dec(x_381);
if (x_418 == 0)
{
uint8_t x_419; 
x_419 = lean_ctor_get_uint8(x_388, 16);
lean_dec(x_388);
if (x_419 == 0)
{
uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_421 = lean_ctor_get(x_3, 1);
lean_inc(x_421);
x_422 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_379);
x_423 = l_Lean_RBNode_findCore___redArg(x_422, x_421, x_379);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; 
lean_dec(x_386);
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_390)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_390;
}
lean_ctor_set(x_424, 0, x_1);
lean_ctor_set(x_424, 1, x_389);
return x_424;
}
else
{
lean_dec(x_423);
lean_dec(x_390);
lean_dec(x_1);
x_391 = x_3;
x_392 = x_420;
x_393 = x_4;
x_394 = x_5;
x_395 = x_6;
goto block_411;
}
}
else
{
lean_dec(x_390);
lean_dec(x_1);
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
goto block_417;
}
}
else
{
lean_dec(x_390);
lean_dec(x_388);
lean_dec(x_1);
x_412 = x_3;
x_413 = x_4;
x_414 = x_5;
x_415 = x_6;
goto block_417;
}
block_411:
{
if (x_392 == 0)
{
lean_dec(x_379);
x_1 = x_386;
x_3 = x_391;
x_4 = x_393;
x_5 = x_394;
x_6 = x_395;
x_7 = x_389;
goto _start;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_397 = lean_st_ref_take(x_393, x_389);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_398, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 4);
lean_inc(x_404);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 lean_ctor_release(x_398, 2);
 lean_ctor_release(x_398, 3);
 lean_ctor_release(x_398, 4);
 x_405 = x_398;
} else {
 lean_dec_ref(x_398);
 x_405 = lean_box(0);
}
x_406 = l_Lean_FVarIdSet_insert(x_402, x_379);
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(0, 5, 0);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_400);
lean_ctor_set(x_407, 1, x_401);
lean_ctor_set(x_407, 2, x_406);
lean_ctor_set(x_407, 3, x_403);
lean_ctor_set(x_407, 4, x_404);
x_408 = lean_st_ref_set(x_393, x_407, x_399);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
x_1 = x_386;
x_3 = x_391;
x_4 = x_393;
x_5 = x_394;
x_6 = x_395;
x_7 = x_409;
goto _start;
}
}
block_417:
{
uint8_t x_416; 
x_416 = lean_ctor_get_uint8(x_412, sizeof(void*)*7 + 8);
x_391 = x_412;
x_392 = x_416;
x_393 = x_413;
x_394 = x_414;
x_395 = x_415;
goto block_411;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_425 = lean_ctor_get(x_380, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_380, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_427 = x_380;
} else {
 lean_dec_ref(x_380);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
case 2:
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_1, 0);
lean_inc(x_429);
x_430 = l_Lean_getExprMVarAssignment_x3f___redArg(x_373, x_374, x_429);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_431 = lean_apply_5(x_430, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_434 = x_431;
} else {
 lean_dec_ref(x_431);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_1);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_1);
x_436 = lean_ctor_get(x_431, 1);
lean_inc(x_436);
lean_dec(x_431);
x_437 = lean_ctor_get(x_432, 0);
lean_inc(x_437);
lean_dec(x_432);
x_1 = x_437;
x_7 = x_436;
goto _start;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_439 = lean_ctor_get(x_431, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_431, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_441 = x_431;
} else {
 lean_dec_ref(x_431);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
case 3:
{
lean_object* x_443; 
lean_dec(x_373);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_1);
lean_ctor_set(x_443, 1, x_7);
return x_443;
}
case 6:
{
lean_object* x_444; 
lean_dec(x_373);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_1);
lean_ctor_set(x_444, 1, x_7);
return x_444;
}
case 7:
{
lean_object* x_445; 
lean_dec(x_373);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_1);
lean_ctor_set(x_445, 1, x_7);
return x_445;
}
case 9:
{
lean_object* x_446; 
lean_dec(x_373);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_1);
lean_ctor_set(x_446, 1, x_7);
return x_446;
}
case 10:
{
lean_object* x_447; 
lean_dec(x_373);
x_447 = lean_ctor_get(x_1, 1);
lean_inc(x_447);
lean_dec(x_1);
x_1 = x_447;
goto _start;
}
default: 
{
lean_object* x_449; 
lean_dec(x_373);
x_449 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_449;
}
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_450 = lean_ctor_get(x_8, 0);
lean_inc(x_450);
lean_dec(x_8);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 3);
lean_inc(x_453);
x_454 = lean_ctor_get(x_450, 4);
lean_inc(x_454);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 lean_ctor_release(x_450, 2);
 lean_ctor_release(x_450, 3);
 lean_ctor_release(x_450, 4);
 x_455 = x_450;
} else {
 lean_dec_ref(x_450);
 x_455 = lean_box(0);
}
x_456 = l_Lean_Meta_whnfEasyCases___closed__2;
x_457 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_451);
x_458 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_458, 0, x_451);
x_459 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_459, 0, x_451);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_461, 0, x_454);
x_462 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_462, 0, x_453);
x_463 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_463, 0, x_452);
if (lean_is_scalar(x_455)) {
 x_464 = lean_alloc_ctor(0, 5, 0);
} else {
 x_464 = x_455;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_456);
lean_ctor_set(x_464, 2, x_463);
lean_ctor_set(x_464, 3, x_462);
lean_ctor_set(x_464, 4, x_461);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_457);
x_466 = l_ReaderT_instMonad___redArg(x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 2);
lean_inc(x_470);
x_471 = lean_ctor_get(x_467, 3);
lean_inc(x_471);
x_472 = lean_ctor_get(x_467, 4);
lean_inc(x_472);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 lean_ctor_release(x_467, 4);
 x_473 = x_467;
} else {
 lean_dec_ref(x_467);
 x_473 = lean_box(0);
}
x_474 = l_Lean_Meta_whnfEasyCases___closed__4;
x_475 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_469);
x_476 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_476, 0, x_469);
x_477 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_477, 0, x_469);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_479, 0, x_472);
x_480 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_480, 0, x_471);
x_481 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_481, 0, x_470);
if (lean_is_scalar(x_473)) {
 x_482 = lean_alloc_ctor(0, 5, 0);
} else {
 x_482 = x_473;
}
lean_ctor_set(x_482, 0, x_478);
lean_ctor_set(x_482, 1, x_474);
lean_ctor_set(x_482, 2, x_481);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set(x_482, 4, x_479);
if (lean_is_scalar(x_468)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_468;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_475);
x_484 = l_Lean_Meta_instMonadMCtxMetaM;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_483);
lean_dec(x_2);
lean_dec(x_1);
x_485 = l_Lean_Meta_whnfEasyCases___closed__6;
x_486 = l_Lean_Meta_whnfEasyCases___closed__10;
x_487 = l_panic___redArg(x_485, x_486);
x_488 = lean_apply_5(x_487, x_3, x_4, x_5, x_6, x_7);
return x_488;
}
case 1:
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_483);
x_489 = lean_ctor_get(x_1, 0);
lean_inc(x_489);
lean_inc(x_3);
lean_inc(x_489);
x_490 = l_Lean_FVarId_getDecl___redArg(x_489, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_491);
lean_dec(x_489);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_493 = x_490;
} else {
 lean_dec_ref(x_490);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_1);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_528; 
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
lean_dec(x_490);
x_496 = lean_ctor_get(x_491, 4);
lean_inc(x_496);
x_497 = l_Lean_Meta_getConfig___redArg(x_3, x_495);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_500 = x_497;
} else {
 lean_dec_ref(x_497);
 x_500 = lean_box(0);
}
x_528 = l_Lean_LocalDecl_isImplementationDetail(x_491);
lean_dec(x_491);
if (x_528 == 0)
{
uint8_t x_529; 
x_529 = lean_ctor_get_uint8(x_498, 16);
lean_dec(x_498);
if (x_529 == 0)
{
uint8_t x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_531 = lean_ctor_get(x_3, 1);
lean_inc(x_531);
x_532 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___lam__0___boxed), 2, 0);
lean_inc(x_489);
x_533 = l_Lean_RBNode_findCore___redArg(x_532, x_531, x_489);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; 
lean_dec(x_496);
lean_dec(x_489);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_500)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_500;
}
lean_ctor_set(x_534, 0, x_1);
lean_ctor_set(x_534, 1, x_499);
return x_534;
}
else
{
lean_dec(x_533);
lean_dec(x_500);
lean_dec(x_1);
x_501 = x_3;
x_502 = x_530;
x_503 = x_4;
x_504 = x_5;
x_505 = x_6;
goto block_521;
}
}
else
{
lean_dec(x_500);
lean_dec(x_1);
x_522 = x_3;
x_523 = x_4;
x_524 = x_5;
x_525 = x_6;
goto block_527;
}
}
else
{
lean_dec(x_500);
lean_dec(x_498);
lean_dec(x_1);
x_522 = x_3;
x_523 = x_4;
x_524 = x_5;
x_525 = x_6;
goto block_527;
}
block_521:
{
if (x_502 == 0)
{
lean_dec(x_489);
x_1 = x_496;
x_3 = x_501;
x_4 = x_503;
x_5 = x_504;
x_6 = x_505;
x_7 = x_499;
goto _start;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_507 = lean_st_ref_take(x_503, x_499);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_508, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_508, 3);
lean_inc(x_513);
x_514 = lean_ctor_get(x_508, 4);
lean_inc(x_514);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 lean_ctor_release(x_508, 2);
 lean_ctor_release(x_508, 3);
 lean_ctor_release(x_508, 4);
 x_515 = x_508;
} else {
 lean_dec_ref(x_508);
 x_515 = lean_box(0);
}
x_516 = l_Lean_FVarIdSet_insert(x_512, x_489);
if (lean_is_scalar(x_515)) {
 x_517 = lean_alloc_ctor(0, 5, 0);
} else {
 x_517 = x_515;
}
lean_ctor_set(x_517, 0, x_510);
lean_ctor_set(x_517, 1, x_511);
lean_ctor_set(x_517, 2, x_516);
lean_ctor_set(x_517, 3, x_513);
lean_ctor_set(x_517, 4, x_514);
x_518 = lean_st_ref_set(x_503, x_517, x_509);
x_519 = lean_ctor_get(x_518, 1);
lean_inc(x_519);
lean_dec(x_518);
x_1 = x_496;
x_3 = x_501;
x_4 = x_503;
x_5 = x_504;
x_6 = x_505;
x_7 = x_519;
goto _start;
}
}
block_527:
{
uint8_t x_526; 
x_526 = lean_ctor_get_uint8(x_522, sizeof(void*)*7 + 8);
x_501 = x_522;
x_502 = x_526;
x_503 = x_523;
x_504 = x_524;
x_505 = x_525;
goto block_521;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_489);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_535 = lean_ctor_get(x_490, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_490, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_537 = x_490;
} else {
 lean_dec_ref(x_490);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
case 2:
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_1, 0);
lean_inc(x_539);
x_540 = l_Lean_getExprMVarAssignment_x3f___redArg(x_483, x_484, x_539);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_541 = lean_apply_5(x_540, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_544 = x_541;
} else {
 lean_dec_ref(x_541);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_1);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
else
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_1);
x_546 = lean_ctor_get(x_541, 1);
lean_inc(x_546);
lean_dec(x_541);
x_547 = lean_ctor_get(x_542, 0);
lean_inc(x_547);
lean_dec(x_542);
x_1 = x_547;
x_7 = x_546;
goto _start;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_549 = lean_ctor_get(x_541, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_541, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_551 = x_541;
} else {
 lean_dec_ref(x_541);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
case 3:
{
lean_object* x_553; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_1);
lean_ctor_set(x_553, 1, x_7);
return x_553;
}
case 6:
{
lean_object* x_554; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_1);
lean_ctor_set(x_554, 1, x_7);
return x_554;
}
case 7:
{
lean_object* x_555; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_1);
lean_ctor_set(x_555, 1, x_7);
return x_555;
}
case 9:
{
lean_object* x_556; 
lean_dec(x_483);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_1);
lean_ctor_set(x_556, 1, x_7);
return x_556;
}
case 10:
{
lean_object* x_557; 
lean_dec(x_483);
x_557 = lean_ctor_get(x_1, 1);
lean_inc(x_557);
lean_dec(x_1);
x_1 = x_557;
goto _start;
}
default: 
{
lean_object* x_559; 
lean_dec(x_483);
x_559 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_559;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_whnfEasyCases___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_ConstantInfo_levelParams(x_1);
x_11 = l_List_lengthTR___redArg(x_10);
lean_dec(x_10);
x_12 = l_List_lengthTR___redArg(x_2);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_6(x_4, x_17, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_ConstantInfo_levelParams(x_1);
x_13 = l_List_lengthTR___redArg(x_12);
lean_dec(x_12);
x_14 = l_List_lengthTR___redArg(x_2);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_4, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Expr_betaRev(x_19, x_3, x_22, x_6);
x_24 = lean_apply_6(x_5, x_23, x_7, x_8, x_9, x_10, x_20);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___redArg(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0;
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_10);
goto block_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1;
x_15 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_16, x_10, x_2, x_3, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
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
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
goto block_7;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
goto block_7;
}
}
else
{
lean_dec(x_1);
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___boxed), 1, 0);
x_6 = lean_find_expr(x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___boxed), 4, 0);
x_10 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_9, x_8, x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Char", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNatAux", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__3;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decEq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hasDecEq", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__9;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt64", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__1;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__22;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__22;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__26;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__25;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__29;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__28;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_canUnfoldAtMatcher___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__6;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_ctor_get_uint8(x_1, 9);
x_7 = lean_box(x_6);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_ConstantInfo_name(x_2);
x_11 = l_Lean_isIrreducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__0(x_10, x_3, x_4, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(1);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(1);
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
x_22 = lean_box(0);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
default: 
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_7);
x_26 = l_Lean_ConstantInfo_name(x_2);
lean_inc(x_26);
x_27 = l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(x_26, x_3, x_4, x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_38; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_st_ref_get(x_4, x_30);
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
x_38 = lean_unbox(x_29);
lean_dec(x_29);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_inc(x_26);
x_40 = lean_is_instance(x_39, x_26);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_111; uint8_t x_112; 
lean_dec(x_34);
x_41 = lean_st_ref_get(x_4, x_33);
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
x_111 = lean_ctor_get(x_42, 0);
lean_inc(x_111);
lean_dec(x_42);
lean_inc(x_26);
x_112 = lean_has_match_pattern_attribute(x_111, x_26);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
lean_free_object(x_27);
x_113 = l_Lean_Meta_canUnfoldAtMatcher___closed__31;
x_114 = lean_name_eq(x_26, x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lean_Meta_canUnfoldAtMatcher___closed__33;
x_116 = lean_name_eq(x_26, x_115);
x_45 = x_116;
goto block_110;
}
else
{
x_45 = x_114;
goto block_110;
}
}
else
{
lean_object* x_117; 
lean_dec(x_44);
lean_dec(x_26);
x_117 = lean_box(x_112);
lean_ctor_set(x_27, 1, x_43);
lean_ctor_set(x_27, 0, x_117);
return x_27;
}
block_110:
{
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_canUnfoldAtMatcher___closed__2;
x_47 = lean_name_eq(x_26, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_canUnfoldAtMatcher___closed__4;
x_49 = lean_name_eq(x_26, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Meta_canUnfoldAtMatcher___closed__7;
x_51 = lean_name_eq(x_26, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Meta_canUnfoldAtMatcher___closed__10;
x_53 = lean_name_eq(x_26, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Meta_canUnfoldAtMatcher___closed__12;
x_55 = lean_name_eq(x_26, x_54);
if (x_55 == 0)
{
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_canUnfoldAtMatcher___closed__14;
x_57 = lean_name_eq(x_26, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Meta_canUnfoldAtMatcher___closed__15;
x_59 = lean_name_eq(x_26, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Meta_canUnfoldAtMatcher___closed__17;
x_61 = lean_name_eq(x_26, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Meta_canUnfoldAtMatcher___closed__18;
x_63 = lean_name_eq(x_26, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Meta_canUnfoldAtMatcher___closed__20;
x_65 = lean_name_eq(x_26, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Meta_canUnfoldAtMatcher___closed__21;
x_67 = lean_name_eq(x_26, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Meta_canUnfoldAtMatcher___closed__23;
x_69 = lean_name_eq(x_26, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Meta_canUnfoldAtMatcher___closed__24;
x_71 = lean_name_eq(x_26, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Meta_canUnfoldAtMatcher___closed__27;
x_73 = lean_name_eq(x_26, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lean_Meta_canUnfoldAtMatcher___closed__30;
x_75 = lean_name_eq(x_26, x_74);
lean_dec(x_26);
x_76 = lean_box(x_75);
if (lean_is_scalar(x_44)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_44;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_43);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_26);
x_78 = lean_box(x_73);
if (lean_is_scalar(x_44)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_44;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_43);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_26);
x_80 = lean_box(x_71);
if (lean_is_scalar(x_44)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_44;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_43);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_26);
x_82 = lean_box(x_69);
if (lean_is_scalar(x_44)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_44;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_43);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_26);
x_84 = lean_box(x_67);
if (lean_is_scalar(x_44)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_44;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_43);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_26);
x_86 = lean_box(x_65);
if (lean_is_scalar(x_44)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_44;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_43);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_26);
x_88 = lean_box(x_63);
if (lean_is_scalar(x_44)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_44;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_43);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_26);
x_90 = lean_box(x_61);
if (lean_is_scalar(x_44)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_44;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_43);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_26);
x_92 = lean_box(x_59);
if (lean_is_scalar(x_44)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_44;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_43);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_26);
x_94 = lean_box(x_57);
if (lean_is_scalar(x_44)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_44;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_43);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_26);
x_96 = lean_box(x_55);
if (lean_is_scalar(x_44)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_44;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_43);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_26);
x_98 = lean_box(x_55);
if (lean_is_scalar(x_44)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_44;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_43);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_26);
x_100 = lean_box(x_53);
if (lean_is_scalar(x_44)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_44;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_43);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_26);
x_102 = lean_box(x_51);
if (lean_is_scalar(x_44)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_44;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_43);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_26);
x_104 = lean_box(x_49);
if (lean_is_scalar(x_44)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_44;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_43);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_26);
x_106 = lean_box(x_47);
if (lean_is_scalar(x_44)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_44;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_43);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_26);
x_108 = lean_box(x_45);
if (lean_is_scalar(x_44)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_44;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_43);
return x_109;
}
}
}
else
{
lean_free_object(x_27);
lean_dec(x_26);
goto block_37;
}
}
else
{
lean_dec(x_32);
lean_free_object(x_27);
lean_dec(x_26);
goto block_37;
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(1);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_127; 
x_118 = lean_ctor_get(x_27, 0);
x_119 = lean_ctor_get(x_27, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_27);
x_120 = lean_st_ref_get(x_4, x_119);
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
x_127 = lean_unbox(x_118);
lean_dec(x_118);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
lean_dec(x_121);
lean_inc(x_26);
x_129 = lean_is_instance(x_128, x_26);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_200; uint8_t x_201; 
lean_dec(x_123);
x_130 = lean_st_ref_get(x_4, x_122);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_200 = lean_ctor_get(x_131, 0);
lean_inc(x_200);
lean_dec(x_131);
lean_inc(x_26);
x_201 = lean_has_match_pattern_attribute(x_200, x_26);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Lean_Meta_canUnfoldAtMatcher___closed__31;
x_203 = lean_name_eq(x_26, x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Lean_Meta_canUnfoldAtMatcher___closed__33;
x_205 = lean_name_eq(x_26, x_204);
x_134 = x_205;
goto block_199;
}
else
{
x_134 = x_203;
goto block_199;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_133);
lean_dec(x_26);
x_206 = lean_box(x_201);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_132);
return x_207;
}
block_199:
{
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = l_Lean_Meta_canUnfoldAtMatcher___closed__2;
x_136 = lean_name_eq(x_26, x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_Meta_canUnfoldAtMatcher___closed__4;
x_138 = lean_name_eq(x_26, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = l_Lean_Meta_canUnfoldAtMatcher___closed__7;
x_140 = lean_name_eq(x_26, x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = l_Lean_Meta_canUnfoldAtMatcher___closed__10;
x_142 = lean_name_eq(x_26, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = l_Lean_Meta_canUnfoldAtMatcher___closed__12;
x_144 = lean_name_eq(x_26, x_143);
if (x_144 == 0)
{
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Lean_Meta_canUnfoldAtMatcher___closed__14;
x_146 = lean_name_eq(x_26, x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Lean_Meta_canUnfoldAtMatcher___closed__15;
x_148 = lean_name_eq(x_26, x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_Meta_canUnfoldAtMatcher___closed__17;
x_150 = lean_name_eq(x_26, x_149);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_Meta_canUnfoldAtMatcher___closed__18;
x_152 = lean_name_eq(x_26, x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_Meta_canUnfoldAtMatcher___closed__20;
x_154 = lean_name_eq(x_26, x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = l_Lean_Meta_canUnfoldAtMatcher___closed__21;
x_156 = lean_name_eq(x_26, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Lean_Meta_canUnfoldAtMatcher___closed__23;
x_158 = lean_name_eq(x_26, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_Meta_canUnfoldAtMatcher___closed__24;
x_160 = lean_name_eq(x_26, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l_Lean_Meta_canUnfoldAtMatcher___closed__27;
x_162 = lean_name_eq(x_26, x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; 
x_163 = l_Lean_Meta_canUnfoldAtMatcher___closed__30;
x_164 = lean_name_eq(x_26, x_163);
lean_dec(x_26);
x_165 = lean_box(x_164);
if (lean_is_scalar(x_133)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_133;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_132);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_26);
x_167 = lean_box(x_162);
if (lean_is_scalar(x_133)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_133;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_132);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_26);
x_169 = lean_box(x_160);
if (lean_is_scalar(x_133)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_133;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_132);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_26);
x_171 = lean_box(x_158);
if (lean_is_scalar(x_133)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_133;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_132);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_26);
x_173 = lean_box(x_156);
if (lean_is_scalar(x_133)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_133;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_132);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_26);
x_175 = lean_box(x_154);
if (lean_is_scalar(x_133)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_133;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_132);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_26);
x_177 = lean_box(x_152);
if (lean_is_scalar(x_133)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_133;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_132);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_26);
x_179 = lean_box(x_150);
if (lean_is_scalar(x_133)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_133;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_132);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_26);
x_181 = lean_box(x_148);
if (lean_is_scalar(x_133)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_133;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_132);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_26);
x_183 = lean_box(x_146);
if (lean_is_scalar(x_133)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_133;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_132);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_26);
x_185 = lean_box(x_144);
if (lean_is_scalar(x_133)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_133;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_132);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_26);
x_187 = lean_box(x_144);
if (lean_is_scalar(x_133)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_133;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_132);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_26);
x_189 = lean_box(x_142);
if (lean_is_scalar(x_133)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_133;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_132);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_26);
x_191 = lean_box(x_140);
if (lean_is_scalar(x_133)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_133;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_132);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_26);
x_193 = lean_box(x_138);
if (lean_is_scalar(x_133)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_133;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_132);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_26);
x_195 = lean_box(x_136);
if (lean_is_scalar(x_133)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_133;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_132);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_26);
x_197 = lean_box(x_134);
if (lean_is_scalar(x_133)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_133;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_132);
return x_198;
}
}
}
else
{
lean_dec(x_26);
goto block_126;
}
}
else
{
lean_dec(x_121);
lean_dec(x_26);
goto block_126;
}
block_126:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_box(1);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_canUnfoldAtMatcher(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_canUnfoldAtMatcher___boxed), 5, 0);
return x_1;
}
}
static uint64_t _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(3);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_getTransparency___redArg(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
switch (lean_obj_tag(x_8)) {
case 2:
{
goto block_90;
}
case 3:
{
goto block_90;
}
default: 
{
lean_object* x_91; 
lean_dec(x_8);
x_91 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_9);
return x_91;
}
}
block_90:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_13 = lean_ctor_get(x_2, 6);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_box(3);
x_16 = lean_unbox(x_15);
lean_ctor_set_uint8(x_11, 9, x_16);
x_17 = 2;
x_18 = lean_uint64_shift_right(x_12, x_17);
x_19 = lean_uint64_shift_left(x_18, x_17);
x_20 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_21 = lean_uint64_lor(x_19, x_20);
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2;
lean_ctor_set(x_2, 6, x_22);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_21);
x_23 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_9);
return x_23;
}
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; 
x_24 = lean_ctor_get_uint8(x_11, 0);
x_25 = lean_ctor_get_uint8(x_11, 1);
x_26 = lean_ctor_get_uint8(x_11, 2);
x_27 = lean_ctor_get_uint8(x_11, 3);
x_28 = lean_ctor_get_uint8(x_11, 4);
x_29 = lean_ctor_get_uint8(x_11, 5);
x_30 = lean_ctor_get_uint8(x_11, 6);
x_31 = lean_ctor_get_uint8(x_11, 7);
x_32 = lean_ctor_get_uint8(x_11, 8);
x_33 = lean_ctor_get_uint8(x_11, 10);
x_34 = lean_ctor_get_uint8(x_11, 11);
x_35 = lean_ctor_get_uint8(x_11, 12);
x_36 = lean_ctor_get_uint8(x_11, 13);
x_37 = lean_ctor_get_uint8(x_11, 14);
x_38 = lean_ctor_get_uint8(x_11, 15);
x_39 = lean_ctor_get_uint8(x_11, 16);
x_40 = lean_ctor_get_uint8(x_11, 17);
lean_dec(x_11);
x_41 = lean_box(3);
x_42 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_42, 0, x_24);
lean_ctor_set_uint8(x_42, 1, x_25);
lean_ctor_set_uint8(x_42, 2, x_26);
lean_ctor_set_uint8(x_42, 3, x_27);
lean_ctor_set_uint8(x_42, 4, x_28);
lean_ctor_set_uint8(x_42, 5, x_29);
lean_ctor_set_uint8(x_42, 6, x_30);
lean_ctor_set_uint8(x_42, 7, x_31);
lean_ctor_set_uint8(x_42, 8, x_32);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 9, x_43);
lean_ctor_set_uint8(x_42, 10, x_33);
lean_ctor_set_uint8(x_42, 11, x_34);
lean_ctor_set_uint8(x_42, 12, x_35);
lean_ctor_set_uint8(x_42, 13, x_36);
lean_ctor_set_uint8(x_42, 14, x_37);
lean_ctor_set_uint8(x_42, 15, x_38);
lean_ctor_set_uint8(x_42, 16, x_39);
lean_ctor_set_uint8(x_42, 17, x_40);
x_44 = 2;
x_45 = lean_uint64_shift_right(x_12, x_44);
x_46 = lean_uint64_shift_left(x_45, x_44);
x_47 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_48 = lean_uint64_lor(x_46, x_47);
x_49 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2;
lean_ctor_set(x_2, 6, x_49);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_48);
x_50 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_9);
return x_50;
}
}
else
{
lean_object* x_51; uint64_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_ctor_get(x_2, 4);
x_58 = lean_ctor_get(x_2, 5);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_51);
lean_dec(x_2);
x_61 = lean_ctor_get_uint8(x_51, 0);
x_62 = lean_ctor_get_uint8(x_51, 1);
x_63 = lean_ctor_get_uint8(x_51, 2);
x_64 = lean_ctor_get_uint8(x_51, 3);
x_65 = lean_ctor_get_uint8(x_51, 4);
x_66 = lean_ctor_get_uint8(x_51, 5);
x_67 = lean_ctor_get_uint8(x_51, 6);
x_68 = lean_ctor_get_uint8(x_51, 7);
x_69 = lean_ctor_get_uint8(x_51, 8);
x_70 = lean_ctor_get_uint8(x_51, 10);
x_71 = lean_ctor_get_uint8(x_51, 11);
x_72 = lean_ctor_get_uint8(x_51, 12);
x_73 = lean_ctor_get_uint8(x_51, 13);
x_74 = lean_ctor_get_uint8(x_51, 14);
x_75 = lean_ctor_get_uint8(x_51, 15);
x_76 = lean_ctor_get_uint8(x_51, 16);
x_77 = lean_ctor_get_uint8(x_51, 17);
if (lean_is_exclusive(x_51)) {
 x_78 = x_51;
} else {
 lean_dec_ref(x_51);
 x_78 = lean_box(0);
}
x_79 = lean_box(3);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 0, 18);
} else {
 x_80 = x_78;
}
lean_ctor_set_uint8(x_80, 0, x_61);
lean_ctor_set_uint8(x_80, 1, x_62);
lean_ctor_set_uint8(x_80, 2, x_63);
lean_ctor_set_uint8(x_80, 3, x_64);
lean_ctor_set_uint8(x_80, 4, x_65);
lean_ctor_set_uint8(x_80, 5, x_66);
lean_ctor_set_uint8(x_80, 6, x_67);
lean_ctor_set_uint8(x_80, 7, x_68);
lean_ctor_set_uint8(x_80, 8, x_69);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 9, x_81);
lean_ctor_set_uint8(x_80, 10, x_70);
lean_ctor_set_uint8(x_80, 11, x_71);
lean_ctor_set_uint8(x_80, 12, x_72);
lean_ctor_set_uint8(x_80, 13, x_73);
lean_ctor_set_uint8(x_80, 14, x_74);
lean_ctor_set_uint8(x_80, 15, x_75);
lean_ctor_set_uint8(x_80, 16, x_76);
lean_ctor_set_uint8(x_80, 17, x_77);
x_82 = 2;
x_83 = lean_uint64_shift_right(x_52, x_82);
x_84 = lean_uint64_shift_left(x_83, x_82);
x_85 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_86 = lean_uint64_lor(x_84, x_85);
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2;
x_88 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_54);
lean_ctor_set(x_88, 2, x_55);
lean_ctor_set(x_88, 3, x_56);
lean_ctor_set(x_88, 4, x_57);
lean_ctor_set(x_88, 5, x_58);
lean_ctor_set(x_88, 6, x_87);
lean_ctor_set_uint64(x_88, sizeof(void*)*7, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 9, x_59);
lean_ctor_set_uint8(x_88, sizeof(void*)*7 + 10, x_60);
x_89 = lean_whnf(x_1, x_88, x_3, x_4, x_5, x_9);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_10, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_array_uget(x_8, x_10);
x_19 = lean_expr_eqv(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_nat_add(x_16, x_2);
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_3);
x_21 = 1;
x_22 = lean_usize_add(x_10, x_21);
x_10 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_array_get(x_24, x_4, x_16);
x_26 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_27 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_27);
x_28 = lean_mk_array(x_27, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_27, x_29);
lean_dec(x_27);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_28, x_30);
x_32 = l_Lean_mkAppN(x_25, x_31);
lean_dec(x_31);
x_33 = lean_nat_add(x_6, x_7);
x_34 = lean_array_get_size(x_4);
x_35 = l_Array_toSubarray___redArg(x_4, x_33, x_34);
x_36 = l_Array_ofSubarray___redArg(x_35);
lean_dec(x_35);
x_37 = l_Lean_mkAppN(x_32, x_36);
lean_dec(x_36);
x_38 = l_Lean_Expr_headBeta(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_11, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_array_uget(x_8, x_10);
x_44 = lean_expr_eqv(x_1, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_45 = lean_nat_add(x_42, x_2);
lean_dec(x_42);
lean_inc(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_10, x_47);
x_10 = x_48;
x_11 = x_46;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
x_50 = l_Lean_instInhabitedExpr;
x_51 = lean_array_get(x_50, x_4, x_42);
x_52 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_53 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_53);
x_54 = lean_mk_array(x_53, x_52);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_53, x_55);
lean_dec(x_53);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_54, x_56);
x_58 = l_Lean_mkAppN(x_51, x_57);
lean_dec(x_57);
x_59 = lean_nat_add(x_6, x_7);
x_60 = lean_array_get_size(x_4);
x_61 = l_Array_toSubarray___redArg(x_4, x_59, x_60);
x_62 = l_Array_ofSubarray___redArg(x_61);
lean_dec(x_61);
x_63 = l_Lean_mkAppN(x_58, x_62);
lean_dec(x_62);
x_64 = l_Lean_Expr_headBeta(x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_42);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_12);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_mkAppN(x_1, x_6);
x_14 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher(x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_getAppFn(x_15);
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_array_size(x_6);
x_21 = 0;
lean_inc(x_15);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg(x_17, x_3, x_18, x_4, x_15, x_2, x_5, x_6, x_20, x_21, x_19, x_16);
lean_dec(x_2);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_33);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_8, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(2);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_19 = x_11;
} else {
 lean_dec_ref(x_11);
 x_19 = lean_box(0);
}
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_26 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_26, x_28);
lean_dec(x_26);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_27, x_29);
x_31 = lean_nat_add(x_23, x_28);
lean_dec(x_23);
x_32 = lean_nat_add(x_31, x_24);
lean_dec(x_24);
lean_dec(x_31);
x_33 = lean_array_get_size(x_30);
x_34 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_18);
lean_dec(x_18);
x_35 = lean_nat_add(x_32, x_34);
x_36 = lean_nat_dec_lt(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_58; 
lean_free_object(x_10);
x_58 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_8, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Core_instantiateValueLevelParams(x_59, x_9, x_4, x_5, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_getTransparency___redArg(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
switch (lean_obj_tag(x_65)) {
case 2:
{
goto block_74;
}
case 3:
{
goto block_74;
}
default: 
{
lean_dec(x_65);
x_37 = x_62;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_66;
goto block_57;
}
}
block_74:
{
lean_object* x_67; 
lean_inc(x_5);
lean_inc(x_4);
x_67 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte(x_62, x_4, x_5, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_37 = x_68;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_69;
goto block_57;
}
else
{
uint8_t x_70; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_61);
if (x_75 == 0)
{
return x_61;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_61, 0);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_61);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_58);
if (x_79 == 0)
{
return x_58;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_58, 0);
x_81 = lean_ctor_get(x_58, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_58);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(3);
lean_ctor_set(x_10, 0, x_83);
return x_10;
}
block_57:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_32);
lean_inc(x_30);
x_44 = l_Array_toSubarray___redArg(x_30, x_43, x_32);
x_45 = l_Array_ofSubarray___redArg(x_44);
lean_dec(x_44);
x_46 = l_Lean_mkAppN(x_37, x_45);
lean_dec(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_46);
x_47 = lean_infer_type(x_46, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_34);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lam__0___boxed), 12, 5);
lean_closure_set(x_50, 0, x_46);
lean_closure_set(x_50, 1, x_32);
lean_closure_set(x_50, 2, x_28);
lean_closure_set(x_50, 3, x_30);
lean_closure_set(x_50, 4, x_34);
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_34);
x_52 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_48, x_51, x_50, x_36, x_38, x_39, x_40, x_41, x_49);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_19);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_84 = lean_ctor_get(x_10, 1);
lean_inc(x_84);
lean_dec(x_10);
x_85 = lean_ctor_get(x_18, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_18, 1);
lean_inc(x_86);
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_88 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_88);
x_89 = lean_mk_array(x_88, x_87);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_88, x_90);
lean_dec(x_88);
x_92 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_89, x_91);
x_93 = lean_nat_add(x_85, x_90);
lean_dec(x_85);
x_94 = lean_nat_add(x_93, x_86);
lean_dec(x_86);
lean_dec(x_93);
x_95 = lean_array_get_size(x_92);
x_96 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_18);
lean_dec(x_18);
x_97 = lean_nat_add(x_94, x_96);
x_98 = lean_nat_dec_lt(x_95, x_97);
lean_dec(x_97);
lean_dec(x_95);
if (x_98 == 0)
{
lean_object* x_120; 
x_120 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_8, x_2, x_3, x_4, x_5, x_84);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Core_instantiateValueLevelParams(x_121, x_9, x_4, x_5, x_122);
lean_dec(x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Meta_getTransparency___redArg(x_2, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
switch (lean_obj_tag(x_127)) {
case 2:
{
goto block_136;
}
case 3:
{
goto block_136;
}
default: 
{
lean_dec(x_127);
x_99 = x_124;
x_100 = x_2;
x_101 = x_3;
x_102 = x_4;
x_103 = x_5;
x_104 = x_128;
goto block_119;
}
}
block_136:
{
lean_object* x_129; 
lean_inc(x_5);
lean_inc(x_4);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte(x_124, x_4, x_5, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_99 = x_130;
x_100 = x_2;
x_101 = x_3;
x_102 = x_4;
x_103 = x_5;
x_104 = x_131;
goto block_119;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_123, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_123, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_139 = x_123;
} else {
 lean_dec_ref(x_123);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_ctor_get(x_120, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_120, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_143 = x_120;
} else {
 lean_dec_ref(x_120);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_box(3);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_84);
return x_146;
}
block_119:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_unsigned_to_nat(0u);
lean_inc(x_94);
lean_inc(x_92);
x_106 = l_Array_toSubarray___redArg(x_92, x_105, x_94);
x_107 = l_Array_ofSubarray___redArg(x_106);
lean_dec(x_106);
x_108 = l_Lean_mkAppN(x_99, x_107);
lean_dec(x_107);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_108);
x_109 = lean_infer_type(x_108, x_100, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_96);
x_112 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lam__0___boxed), 12, 5);
lean_closure_set(x_112, 0, x_108);
lean_closure_set(x_112, 1, x_94);
lean_closure_set(x_112, 2, x_90);
lean_closure_set(x_112, 3, x_92);
lean_closure_set(x_112, 4, x_96);
if (lean_is_scalar(x_19)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_19;
}
lean_ctor_set(x_113, 0, x_96);
x_114 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_110, x_113, x_112, x_98, x_100, x_101, x_102, x_103, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_19);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_box(2);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_6);
return x_148;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_14, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_reduceMatcher_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_18, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_reduceMatcher_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_toCtorIfLit(x_1);
x_10 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Environment_find_x3f(x_16, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_free_object(x_12);
lean_dec(x_9);
x_5 = x_15;
goto block_8;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Expr_getAppNumArgs(x_9);
x_25 = lean_nat_add(x_23, x_2);
lean_dec(x_23);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_19);
lean_dec(x_9);
x_27 = lean_box(0);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_nat_sub(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Expr_getRevArg_x21(x_9, x_30);
lean_dec(x_9);
lean_ctor_set(x_19, 0, x_31);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
else
{
lean_free_object(x_19);
lean_dec(x_21);
lean_free_object(x_12);
lean_dec(x_9);
x_5 = x_15;
goto block_8;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
if (lean_obj_tag(x_32) == 6)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Expr_getAppNumArgs(x_9);
x_36 = lean_nat_add(x_34, x_2);
lean_dec(x_34);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_9);
x_38 = lean_box(0);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_nat_sub(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_39, x_40);
lean_dec(x_39);
x_42 = l_Lean_Expr_getRevArg_x21(x_9, x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
}
else
{
lean_dec(x_32);
lean_free_object(x_12);
lean_dec(x_9);
x_5 = x_15;
goto block_8;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Environment_find_x3f(x_46, x_11, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_9);
x_5 = x_45;
goto block_8;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_obj_tag(x_50) == 6)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Expr_getAppNumArgs(x_9);
x_55 = lean_nat_add(x_53, x_2);
lean_dec(x_53);
x_56 = lean_nat_dec_lt(x_55, x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_9);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_45);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_nat_sub(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_59);
x_62 = l_Lean_Expr_getRevArg_x21(x_9, x_61);
lean_dec(x_9);
if (lean_is_scalar(x_51)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_51;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
return x_64;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_9);
x_5 = x_45;
goto block_8;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
x_5 = x_4;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_projectCore_x3f___redArg(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_projectCore_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_projectCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_projectCore_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = lean_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_projectCore_x3f___redArg(x_9, x_2, x_6, x_10);
lean_dec(x_6);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_project_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_project_x3f(x_8, x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_mvarId_x21(x_1);
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg(x_11, x_4, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
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
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_28 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_28);
x_29 = lean_mk_array(x_28, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_29, x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_array_get_size(x_25);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_12);
x_36 = l_Lean_Expr_mvar___override(x_26);
x_37 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_36, x_4, x_23);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Expr_hasExprMVar(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_expr_abstract(x_39, x_25);
lean_dec(x_25);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_expr_instantiate_rev_range(x_41, x_42, x_34, x_32);
lean_dec(x_41);
x_44 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_33, x_32, x_34, x_43);
lean_dec(x_32);
lean_dec(x_33);
lean_ctor_set(x_13, 0, x_44);
lean_ctor_set(x_37, 0, x_13);
return x_37;
}
else
{
lean_object* x_45; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_13);
x_45 = lean_box(0);
lean_ctor_set(x_37, 0, x_45);
return x_37;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = l_Lean_Expr_hasExprMVar(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_expr_abstract(x_46, x_25);
lean_dec(x_25);
lean_dec(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_expr_instantiate_rev_range(x_49, x_50, x_34, x_32);
lean_dec(x_49);
x_52 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_33, x_32, x_34, x_51);
lean_dec(x_32);
lean_dec(x_33);
lean_ctor_set(x_13, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_13);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_47);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_13);
x_56 = lean_box(0);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_dec(x_12);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_62 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_62);
x_63 = lean_mk_array(x_62, x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_62, x_64);
lean_dec(x_62);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_63, x_65);
x_67 = lean_array_get_size(x_66);
x_68 = lean_array_get_size(x_59);
x_69 = lean_nat_dec_lt(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = l_Lean_Expr_mvar___override(x_60);
x_71 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_70, x_4, x_58);
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
x_75 = l_Lean_Expr_hasExprMVar(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_expr_abstract(x_72, x_59);
lean_dec(x_59);
lean_dec(x_72);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_expr_instantiate_rev_range(x_76, x_77, x_68, x_66);
lean_dec(x_76);
x_79 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_67, x_66, x_68, x_78);
lean_dec(x_66);
lean_dec(x_67);
lean_ctor_set(x_13, 0, x_79);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_13);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_59);
lean_free_object(x_13);
x_81 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_59);
lean_free_object(x_13);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_58);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_85 = lean_ctor_get(x_13, 0);
lean_inc(x_85);
lean_dec(x_13);
x_86 = lean_ctor_get(x_12, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_87 = x_12;
} else {
 lean_dec_ref(x_12);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_91 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_91);
x_92 = lean_mk_array(x_91, x_90);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_91, x_93);
lean_dec(x_91);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_92, x_94);
x_96 = lean_array_get_size(x_95);
x_97 = lean_array_get_size(x_88);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_87);
x_99 = l_Lean_Expr_mvar___override(x_89);
x_100 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_99, x_4, x_86);
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
x_104 = l_Lean_Expr_hasExprMVar(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_expr_abstract(x_101, x_88);
lean_dec(x_88);
lean_dec(x_101);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_expr_instantiate_rev_range(x_105, x_106, x_97, x_95);
lean_dec(x_105);
x_108 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_96, x_95, x_97, x_107);
lean_dec(x_95);
lean_dec(x_96);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_103)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_103;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_102);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_101);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_88);
x_111 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_103;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_102);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_89);
lean_dec(x_88);
x_113 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_87;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_86);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandLet(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_3);
x_6 = lean_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Expr_letFunAppArgs_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_expr_instantiate_rev(x_19, x_2);
lean_dec(x_19);
x_22 = lean_array_push(x_2, x_21);
x_1 = x_20;
x_2 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_ConstantInfo_levelParams(x_2);
x_12 = l_List_lengthTR___redArg(x_11);
lean_dec(x_11);
x_13 = l_List_lengthTR___redArg(x_3);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Lean_Core_instantiateValueLevelParams(x_2, x_3, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Expr_betaRev(x_17, x_4, x_20, x_5);
x_22 = l_Lean_Meta_whnfCore_go(x_21, x_6, x_7, x_8, x_9, x_18);
return x_22;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_whnfCore_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_whnfEasyCases___closed__6;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_ConstantInfo_name(x_1);
x_9 = l_Lean_Meta_recordUnfold___redArg(x_8, x_4, x_5, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_whnfCore_go(x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.whnfCore.go", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(663u);
x_4 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1;
x_5 = l_Lean_Meta_whnfEasyCases___closed__7;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whnf", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_1);
x_258 = l_Lean_Meta_whnfEasyCases___closed__10;
x_259 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_258, x_2, x_3, x_4, x_5, x_6);
return x_259;
}
case 1:
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_1, 0);
lean_inc(x_260);
lean_inc(x_2);
lean_inc(x_260);
x_261 = l_Lean_FVarId_getDecl___redArg(x_260, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_261);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_261, 0);
lean_dec(x_264);
lean_ctor_set(x_261, 0, x_1);
return x_261;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
lean_dec(x_261);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_1);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_dec(x_261);
x_268 = lean_ctor_get(x_262, 4);
lean_inc(x_268);
x_269 = l_Lean_Meta_getConfig___redArg(x_2, x_267);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_305; 
x_271 = lean_ctor_get(x_269, 0);
x_272 = lean_ctor_get(x_269, 1);
x_305 = l_Lean_LocalDecl_isImplementationDetail(x_262);
lean_dec(x_262);
if (x_305 == 0)
{
uint8_t x_306; 
x_306 = lean_ctor_get_uint8(x_271, 16);
lean_dec(x_271);
if (x_306 == 0)
{
uint8_t x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_308 = lean_ctor_get(x_2, 1);
lean_inc(x_308);
x_309 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_308, x_260);
lean_dec(x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_269, 0, x_1);
return x_269;
}
else
{
lean_dec(x_309);
lean_free_object(x_269);
lean_dec(x_1);
x_273 = x_2;
x_274 = x_307;
x_275 = x_3;
x_276 = x_4;
x_277 = x_5;
goto block_298;
}
}
else
{
lean_free_object(x_269);
lean_dec(x_1);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
goto block_304;
}
}
else
{
lean_free_object(x_269);
lean_dec(x_271);
lean_dec(x_1);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
goto block_304;
}
block_298:
{
if (x_274 == 0)
{
lean_dec(x_260);
x_1 = x_268;
x_2 = x_273;
x_3 = x_275;
x_4 = x_276;
x_5 = x_277;
x_6 = x_272;
goto _start;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_279 = lean_st_ref_take(x_275, x_272);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_ctor_get(x_280, 2);
x_284 = l_Lean_FVarIdSet_insert(x_283, x_260);
lean_ctor_set(x_280, 2, x_284);
x_285 = lean_st_ref_set(x_275, x_280, x_281);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_1 = x_268;
x_2 = x_273;
x_3 = x_275;
x_4 = x_276;
x_5 = x_277;
x_6 = x_286;
goto _start;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_288 = lean_ctor_get(x_280, 0);
x_289 = lean_ctor_get(x_280, 1);
x_290 = lean_ctor_get(x_280, 2);
x_291 = lean_ctor_get(x_280, 3);
x_292 = lean_ctor_get(x_280, 4);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_280);
x_293 = l_Lean_FVarIdSet_insert(x_290, x_260);
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_289);
lean_ctor_set(x_294, 2, x_293);
lean_ctor_set(x_294, 3, x_291);
lean_ctor_set(x_294, 4, x_292);
x_295 = lean_st_ref_set(x_275, x_294, x_281);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_1 = x_268;
x_2 = x_273;
x_3 = x_275;
x_4 = x_276;
x_5 = x_277;
x_6 = x_296;
goto _start;
}
}
}
block_304:
{
uint8_t x_303; 
x_303 = lean_ctor_get_uint8(x_299, sizeof(void*)*7 + 8);
x_273 = x_299;
x_274 = x_303;
x_275 = x_300;
x_276 = x_301;
x_277 = x_302;
goto block_298;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_339; 
x_310 = lean_ctor_get(x_269, 0);
x_311 = lean_ctor_get(x_269, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_269);
x_339 = l_Lean_LocalDecl_isImplementationDetail(x_262);
lean_dec(x_262);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = lean_ctor_get_uint8(x_310, 16);
lean_dec(x_310);
if (x_340 == 0)
{
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_342 = lean_ctor_get(x_2, 1);
lean_inc(x_342);
x_343 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_342, x_260);
lean_dec(x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_1);
lean_ctor_set(x_344, 1, x_311);
return x_344;
}
else
{
lean_dec(x_343);
lean_dec(x_1);
x_312 = x_2;
x_313 = x_341;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
goto block_332;
}
}
else
{
lean_dec(x_1);
x_333 = x_2;
x_334 = x_3;
x_335 = x_4;
x_336 = x_5;
goto block_338;
}
}
else
{
lean_dec(x_310);
lean_dec(x_1);
x_333 = x_2;
x_334 = x_3;
x_335 = x_4;
x_336 = x_5;
goto block_338;
}
block_332:
{
if (x_313 == 0)
{
lean_dec(x_260);
x_1 = x_268;
x_2 = x_312;
x_3 = x_314;
x_4 = x_315;
x_5 = x_316;
x_6 = x_311;
goto _start;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_318 = lean_st_ref_take(x_314, x_311);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_319, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 4);
lean_inc(x_325);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 x_326 = x_319;
} else {
 lean_dec_ref(x_319);
 x_326 = lean_box(0);
}
x_327 = l_Lean_FVarIdSet_insert(x_323, x_260);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 5, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_322);
lean_ctor_set(x_328, 2, x_327);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
x_329 = lean_st_ref_set(x_314, x_328, x_320);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_1 = x_268;
x_2 = x_312;
x_3 = x_314;
x_4 = x_315;
x_5 = x_316;
x_6 = x_330;
goto _start;
}
}
block_338:
{
uint8_t x_337; 
x_337 = lean_ctor_get_uint8(x_333, sizeof(void*)*7 + 8);
x_312 = x_333;
x_313 = x_337;
x_314 = x_334;
x_315 = x_335;
x_316 = x_336;
goto block_332;
}
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_261);
if (x_345 == 0)
{
return x_261;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_261, 0);
x_347 = lean_ctor_get(x_261, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_261);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
case 2:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_1, 0);
lean_inc(x_349);
x_350 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(x_349, x_3, x_6);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
uint8_t x_352; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_352 = !lean_is_exclusive(x_350);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_350, 0);
lean_dec(x_353);
lean_ctor_set(x_350, 0, x_1);
return x_350;
}
else
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
lean_dec(x_350);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_1);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_1);
x_356 = lean_ctor_get(x_350, 1);
lean_inc(x_356);
lean_dec(x_350);
x_357 = lean_ctor_get(x_351, 0);
lean_inc(x_357);
lean_dec(x_351);
x_1 = x_357;
x_6 = x_356;
goto _start;
}
}
case 3:
{
lean_object* x_359; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_1);
lean_ctor_set(x_359, 1, x_6);
return x_359;
}
case 6:
{
lean_object* x_360; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_1);
lean_ctor_set(x_360, 1, x_6);
return x_360;
}
case 7:
{
lean_object* x_361; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_1);
lean_ctor_set(x_361, 1, x_6);
return x_361;
}
case 9:
{
lean_object* x_362; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_6);
return x_362;
}
case 10:
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_1, 1);
lean_inc(x_363);
lean_dec(x_1);
x_1 = x_363;
goto _start;
}
default: 
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_365 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
x_366 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_365, x_4, x_6);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_unbox(x_367);
lean_dec(x_367);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
lean_dec(x_366);
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
x_198 = x_5;
x_199 = x_369;
goto block_257;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_370 = lean_ctor_get(x_366, 1);
lean_inc(x_370);
lean_dec(x_366);
lean_inc(x_1);
x_371 = l_Lean_MessageData_ofExpr(x_1);
x_372 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_365, x_371, x_2, x_3, x_4, x_5, x_370);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
x_198 = x_5;
x_199 = x_373;
goto block_257;
}
}
}
block_119:
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_7, 12);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_15);
x_18 = l_Lean_Meta_reduceMatcher_x3f(x_15, x_11, x_12, x_13, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_whnfCore_go(x_21, x_11, x_12, x_13, x_8, x_20);
return x_22;
}
case 2:
{
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_st_ref_get(x_8, x_23);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Environment_find_x3f(x_30, x_24, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_15);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed), 7, 1);
lean_closure_set(x_33, 0, x_15);
switch (lean_obj_tag(x_32)) {
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_33);
lean_free_object(x_26);
x_34 = l_Lean_ConstantInfo_name(x_32);
lean_inc(x_34);
x_35 = l_Lean_Meta_isAuxDef___redArg(x_34, x_8, x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_15);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Meta_recordUnfold___redArg(x_34, x_12, x_13, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Expr_getAppNumArgs(x_15);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
lean_inc(x_15);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_15, x_46);
x_48 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(x_15, x_32, x_25, x_47, x_10, x_11, x_12, x_13, x_8, x_44);
lean_dec(x_47);
lean_dec(x_32);
return x_48;
}
}
case 4:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_26);
lean_dec(x_25);
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_50, 0, x_32);
x_51 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_52 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_52);
x_53 = lean_mk_array(x_52, x_51);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_52, x_54);
lean_dec(x_52);
x_56 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_53, x_55);
x_57 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_49, x_56, x_33, x_50, x_11, x_12, x_13, x_8, x_29);
lean_dec(x_56);
lean_dec(x_49);
return x_57;
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_26);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_59, 0, x_32);
x_60 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_61 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_61);
x_62 = lean_mk_array(x_61, x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_61, x_63);
lean_dec(x_61);
x_65 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_62, x_64);
x_66 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_58, x_25, x_65, x_33, x_59, x_11, x_12, x_13, x_8, x_29);
lean_dec(x_65);
return x_66;
}
default: 
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_26, 0);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_26);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Environment_find_x3f(x_69, x_24, x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_15);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed), 7, 1);
lean_closure_set(x_73, 0, x_15);
switch (lean_obj_tag(x_72)) {
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_73);
x_74 = l_Lean_ConstantInfo_name(x_72);
lean_inc(x_74);
x_75 = l_Lean_Meta_isAuxDef___redArg(x_74, x_8, x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_15);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l_Lean_Meta_recordUnfold___redArg(x_74, x_12, x_13, x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Expr_getAppNumArgs(x_15);
x_85 = lean_mk_empty_array_with_capacity(x_84);
lean_dec(x_84);
lean_inc(x_15);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_15, x_85);
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(x_15, x_72, x_25, x_86, x_10, x_11, x_12, x_13, x_8, x_83);
lean_dec(x_86);
lean_dec(x_72);
return x_87;
}
}
case 4:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_25);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_89, 0, x_72);
x_90 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_91 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_91);
x_92 = lean_mk_array(x_91, x_90);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_91, x_93);
lean_dec(x_91);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_92, x_94);
x_96 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_88, x_95, x_73, x_89, x_11, x_12, x_13, x_8, x_68);
lean_dec(x_95);
lean_dec(x_88);
return x_96;
}
case 7:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_72, 0);
lean_inc(x_97);
x_98 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_98, 0, x_72);
x_99 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_100 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_100);
x_101 = lean_mk_array(x_100, x_99);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_100, x_102);
lean_dec(x_100);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_101, x_103);
x_105 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_97, x_25, x_104, x_73, x_98, x_11, x_12, x_13, x_8, x_68);
lean_dec(x_104);
return x_105;
}
default: 
{
lean_object* x_106; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_15);
lean_ctor_set(x_106, 1, x_68);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_107 = !lean_is_exclusive(x_18);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_18, 0);
lean_dec(x_108);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_18, 1);
lean_inc(x_109);
lean_dec(x_18);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
default: 
{
uint8_t x_111; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_111 = !lean_is_exclusive(x_18);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_18, 0);
lean_dec(x_112);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_18, 1);
lean_inc(x_113);
lean_dec(x_18);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_15);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_115 = !lean_is_exclusive(x_18);
if (x_115 == 0)
{
return x_18;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_18, 0);
x_117 = lean_ctor_get(x_18, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_18);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
block_137:
{
lean_object* x_129; lean_object* x_130; 
lean_inc(x_1);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(x_127, x_1, x_122, x_124, x_125, x_121, x_126);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_expr_eqv(x_123, x_127);
lean_dec(x_123);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = l_Lean_Expr_updateFn(x_1, x_127);
x_7 = x_120;
x_8 = x_121;
x_9 = x_131;
x_10 = x_128;
x_11 = x_122;
x_12 = x_124;
x_13 = x_125;
x_14 = x_127;
x_15 = x_133;
goto block_119;
}
else
{
x_7 = x_120;
x_8 = x_121;
x_9 = x_131;
x_10 = x_128;
x_11 = x_122;
x_12 = x_124;
x_13 = x_125;
x_14 = x_127;
x_15 = x_1;
goto block_119;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_120);
lean_dec(x_1);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
lean_dec(x_130);
x_136 = l_Lean_Meta_whnfCore_go(x_135, x_122, x_124, x_125, x_121, x_134);
return x_136;
}
}
block_152:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_144 = l_Lean_Expr_getAppNumArgs(x_1);
x_145 = lean_mk_empty_array_with_capacity(x_144);
lean_dec(x_144);
x_146 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_145);
x_147 = lean_box(0);
x_148 = lean_unbox(x_147);
x_149 = lean_unbox(x_147);
x_150 = l_Lean_Expr_betaRev(x_143, x_146, x_148, x_149);
lean_dec(x_146);
x_151 = l_Lean_Meta_whnfCore_go(x_150, x_139, x_140, x_141, x_138, x_142);
return x_151;
}
block_162:
{
if (x_161 == 0)
{
x_120 = x_153;
x_121 = x_154;
x_122 = x_155;
x_123 = x_156;
x_124 = x_157;
x_125 = x_158;
x_126 = x_159;
x_127 = x_160;
x_128 = x_161;
goto block_137;
}
else
{
lean_dec(x_156);
lean_dec(x_153);
x_138 = x_154;
x_139 = x_155;
x_140 = x_157;
x_141 = x_158;
x_142 = x_159;
x_143 = x_160;
goto block_152;
}
}
block_177:
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_Expr_getAppFn(x_164);
lean_dec(x_164);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_170);
x_171 = l_Lean_Meta_whnfCore_go(x_170, x_165, x_166, x_167, x_168, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Expr_isLambda(x_172);
if (x_174 == 0)
{
x_153 = x_163;
x_154 = x_168;
x_155 = x_165;
x_156 = x_170;
x_157 = x_166;
x_158 = x_167;
x_159 = x_173;
x_160 = x_172;
x_161 = x_174;
goto block_162;
}
else
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_163, 13);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_isLambda(x_170);
if (x_176 == 0)
{
x_153 = x_163;
x_154 = x_168;
x_155 = x_165;
x_156 = x_170;
x_157 = x_166;
x_158 = x_167;
x_159 = x_173;
x_160 = x_172;
x_161 = x_174;
goto block_162;
}
else
{
x_120 = x_163;
x_121 = x_168;
x_122 = x_165;
x_123 = x_170;
x_124 = x_166;
x_125 = x_167;
x_126 = x_173;
x_127 = x_172;
x_128 = x_175;
goto block_137;
}
}
else
{
lean_dec(x_170);
lean_dec(x_163);
x_138 = x_168;
x_139 = x_165;
x_140 = x_166;
x_141 = x_167;
x_142 = x_173;
x_143 = x_172;
goto block_152;
}
}
}
else
{
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_1);
return x_171;
}
}
block_194:
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Meta_projectCore_x3f___redArg(x_179, x_178, x_183, x_184);
lean_dec(x_178);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
x_187 = !lean_is_exclusive(x_185);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_185, 0);
lean_dec(x_188);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_1);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_dec(x_185);
x_192 = lean_ctor_get(x_186, 0);
lean_inc(x_192);
lean_dec(x_186);
x_193 = l_Lean_Meta_whnfCore_go(x_192, x_180, x_181, x_182, x_183, x_191);
return x_193;
}
}
block_257:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_200; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
case 5:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_1, 0);
lean_inc(x_201);
x_202 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_203, 15);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_163 = x_203;
x_164 = x_201;
x_165 = x_195;
x_166 = x_196;
x_167 = x_197;
x_168 = x_198;
x_169 = x_205;
goto block_177;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
lean_dec(x_202);
lean_inc(x_1);
x_207 = l_Lean_Expr_letFunAppArgs_x3f(x_1);
if (lean_obj_tag(x_207) == 0)
{
x_163 = x_203;
x_164 = x_201;
x_165 = x_195;
x_166 = x_196;
x_167 = x_197;
x_168 = x_198;
x_169 = x_206;
goto block_177;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_1);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_216 = lean_array_push(x_215, x_213);
x_217 = l_Lean_Meta_expandLet(x_214, x_216);
x_218 = l_Lean_mkAppN(x_217, x_212);
lean_dec(x_212);
x_219 = l_Lean_Meta_whnfCore_go(x_218, x_195, x_196, x_197, x_198, x_206);
return x_219;
}
}
}
case 8:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_1, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_1, 3);
lean_inc(x_221);
x_222 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_223, 15);
lean_dec(x_223);
if (x_224 == 0)
{
uint8_t x_225; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_225 = !lean_is_exclusive(x_222);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_222, 0);
lean_dec(x_226);
lean_ctor_set(x_222, 0, x_1);
return x_222;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_dec(x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_1);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_1);
x_229 = lean_ctor_get(x_222, 1);
lean_inc(x_229);
lean_dec(x_222);
x_230 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_231 = lean_array_push(x_230, x_220);
x_232 = l_Lean_Meta_expandLet(x_221, x_231);
x_233 = l_Lean_Meta_whnfCore_go(x_232, x_195, x_196, x_197, x_198, x_229);
return x_233;
}
}
case 11:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_1, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 2);
lean_inc(x_235);
x_236 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get_uint8(x_237, 14);
lean_dec(x_237);
switch (x_238) {
case 0:
{
uint8_t x_239; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_239 = !lean_is_exclusive(x_236);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_236, 0);
lean_dec(x_240);
lean_ctor_set(x_236, 0, x_1);
return x_236;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
case 1:
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_244 = l_Lean_Meta_whnfCore_go(x_235, x_195, x_196, x_197, x_198, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_178 = x_234;
x_179 = x_245;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_246;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_244;
}
}
case 2:
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_236, 1);
lean_inc(x_247);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_248 = lean_whnf(x_235, x_195, x_196, x_197, x_198, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_178 = x_234;
x_179 = x_249;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_250;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_248;
}
}
default: 
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_236, 1);
lean_inc(x_251);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_252 = l_Lean_Meta_whnfAtMostI(x_235, x_195, x_196, x_197, x_198, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_178 = x_234;
x_179 = x_253;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_254;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_252;
}
}
}
}
default: 
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_1);
x_255 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3;
x_256 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_255, x_195, x_196, x_197, x_198, x_199);
return x_256;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_1);
x_258 = l_Lean_Meta_whnfEasyCases___closed__10;
x_259 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_258, x_2, x_3, x_4, x_5, x_6);
return x_259;
}
case 1:
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_1, 0);
lean_inc(x_260);
lean_inc(x_2);
lean_inc(x_260);
x_261 = l_Lean_FVarId_getDecl___redArg(x_260, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_261);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_261, 0);
lean_dec(x_264);
lean_ctor_set(x_261, 0, x_1);
return x_261;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
lean_dec(x_261);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_1);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_dec(x_261);
x_268 = lean_ctor_get(x_262, 4);
lean_inc(x_268);
x_269 = l_Lean_Meta_getConfig___redArg(x_2, x_267);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_305; 
x_271 = lean_ctor_get(x_269, 0);
x_272 = lean_ctor_get(x_269, 1);
x_305 = l_Lean_LocalDecl_isImplementationDetail(x_262);
lean_dec(x_262);
if (x_305 == 0)
{
uint8_t x_306; 
x_306 = lean_ctor_get_uint8(x_271, 16);
lean_dec(x_271);
if (x_306 == 0)
{
uint8_t x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_308 = lean_ctor_get(x_2, 1);
lean_inc(x_308);
x_309 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_308, x_260);
lean_dec(x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_269, 0, x_1);
return x_269;
}
else
{
lean_dec(x_309);
lean_free_object(x_269);
lean_dec(x_1);
x_273 = x_2;
x_274 = x_307;
x_275 = x_3;
x_276 = x_4;
x_277 = x_5;
goto block_298;
}
}
else
{
lean_free_object(x_269);
lean_dec(x_1);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
goto block_304;
}
}
else
{
lean_free_object(x_269);
lean_dec(x_271);
lean_dec(x_1);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
goto block_304;
}
block_298:
{
if (x_274 == 0)
{
lean_object* x_278; 
lean_dec(x_260);
x_278 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_268, x_273, x_275, x_276, x_277, x_272);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_279 = lean_st_ref_take(x_275, x_272);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_280, 2);
x_284 = l_Lean_FVarIdSet_insert(x_283, x_260);
lean_ctor_set(x_280, 2, x_284);
x_285 = lean_st_ref_set(x_275, x_280, x_281);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_268, x_273, x_275, x_276, x_277, x_286);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_288 = lean_ctor_get(x_280, 0);
x_289 = lean_ctor_get(x_280, 1);
x_290 = lean_ctor_get(x_280, 2);
x_291 = lean_ctor_get(x_280, 3);
x_292 = lean_ctor_get(x_280, 4);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_280);
x_293 = l_Lean_FVarIdSet_insert(x_290, x_260);
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_289);
lean_ctor_set(x_294, 2, x_293);
lean_ctor_set(x_294, 3, x_291);
lean_ctor_set(x_294, 4, x_292);
x_295 = lean_st_ref_set(x_275, x_294, x_281);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_297 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_268, x_273, x_275, x_276, x_277, x_296);
return x_297;
}
}
}
block_304:
{
uint8_t x_303; 
x_303 = lean_ctor_get_uint8(x_299, sizeof(void*)*7 + 8);
x_273 = x_299;
x_274 = x_303;
x_275 = x_300;
x_276 = x_301;
x_277 = x_302;
goto block_298;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_339; 
x_310 = lean_ctor_get(x_269, 0);
x_311 = lean_ctor_get(x_269, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_269);
x_339 = l_Lean_LocalDecl_isImplementationDetail(x_262);
lean_dec(x_262);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = lean_ctor_get_uint8(x_310, 16);
lean_dec(x_310);
if (x_340 == 0)
{
uint8_t x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_342 = lean_ctor_get(x_2, 1);
lean_inc(x_342);
x_343 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_342, x_260);
lean_dec(x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_1);
lean_ctor_set(x_344, 1, x_311);
return x_344;
}
else
{
lean_dec(x_343);
lean_dec(x_1);
x_312 = x_2;
x_313 = x_341;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
goto block_332;
}
}
else
{
lean_dec(x_1);
x_333 = x_2;
x_334 = x_3;
x_335 = x_4;
x_336 = x_5;
goto block_338;
}
}
else
{
lean_dec(x_310);
lean_dec(x_1);
x_333 = x_2;
x_334 = x_3;
x_335 = x_4;
x_336 = x_5;
goto block_338;
}
block_332:
{
if (x_313 == 0)
{
lean_object* x_317; 
lean_dec(x_260);
x_317 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_268, x_312, x_314, x_315, x_316, x_311);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_318 = lean_st_ref_take(x_314, x_311);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_319, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 4);
lean_inc(x_325);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 x_326 = x_319;
} else {
 lean_dec_ref(x_319);
 x_326 = lean_box(0);
}
x_327 = l_Lean_FVarIdSet_insert(x_323, x_260);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 5, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_322);
lean_ctor_set(x_328, 2, x_327);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
x_329 = lean_st_ref_set(x_314, x_328, x_320);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_331 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_268, x_312, x_314, x_315, x_316, x_330);
return x_331;
}
}
block_338:
{
uint8_t x_337; 
x_337 = lean_ctor_get_uint8(x_333, sizeof(void*)*7 + 8);
x_312 = x_333;
x_313 = x_337;
x_314 = x_334;
x_315 = x_335;
x_316 = x_336;
goto block_332;
}
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_261);
if (x_345 == 0)
{
return x_261;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_261, 0);
x_347 = lean_ctor_get(x_261, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_261);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
case 2:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_1, 0);
lean_inc(x_349);
x_350 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(x_349, x_3, x_6);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
uint8_t x_352; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_352 = !lean_is_exclusive(x_350);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_350, 0);
lean_dec(x_353);
lean_ctor_set(x_350, 0, x_1);
return x_350;
}
else
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
lean_dec(x_350);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_1);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_1);
x_356 = lean_ctor_get(x_350, 1);
lean_inc(x_356);
lean_dec(x_350);
x_357 = lean_ctor_get(x_351, 0);
lean_inc(x_357);
lean_dec(x_351);
x_358 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_357, x_2, x_3, x_4, x_5, x_356);
return x_358;
}
}
case 3:
{
lean_object* x_359; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_1);
lean_ctor_set(x_359, 1, x_6);
return x_359;
}
case 6:
{
lean_object* x_360; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_1);
lean_ctor_set(x_360, 1, x_6);
return x_360;
}
case 7:
{
lean_object* x_361; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_1);
lean_ctor_set(x_361, 1, x_6);
return x_361;
}
case 9:
{
lean_object* x_362; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_6);
return x_362;
}
case 10:
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_1, 1);
lean_inc(x_363);
lean_dec(x_1);
x_364 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2(x_363, x_2, x_3, x_4, x_5, x_6);
return x_364;
}
default: 
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_365 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
x_366 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_365, x_4, x_6);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_unbox(x_367);
lean_dec(x_367);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
lean_dec(x_366);
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
x_198 = x_5;
x_199 = x_369;
goto block_257;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_370 = lean_ctor_get(x_366, 1);
lean_inc(x_370);
lean_dec(x_366);
lean_inc(x_1);
x_371 = l_Lean_MessageData_ofExpr(x_1);
x_372 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_365, x_371, x_2, x_3, x_4, x_5, x_370);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
x_198 = x_5;
x_199 = x_373;
goto block_257;
}
}
}
block_119:
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_13, 12);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_9);
lean_inc(x_10);
lean_inc(x_12);
lean_inc(x_14);
lean_inc(x_15);
x_18 = l_Lean_Meta_reduceMatcher_x3f(x_15, x_14, x_12, x_10, x_9, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_8);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_whnfCore_go(x_21, x_14, x_12, x_10, x_9, x_20);
return x_22;
}
case 2:
{
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_st_ref_get(x_9, x_23);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Environment_find_x3f(x_30, x_24, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_15);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed), 7, 1);
lean_closure_set(x_33, 0, x_15);
switch (lean_obj_tag(x_32)) {
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_33);
lean_free_object(x_26);
x_34 = l_Lean_ConstantInfo_name(x_32);
lean_inc(x_34);
x_35 = l_Lean_Meta_isAuxDef___redArg(x_34, x_9, x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_15);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Meta_recordUnfold___redArg(x_34, x_12, x_10, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Expr_getAppNumArgs(x_15);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
lean_inc(x_15);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_15, x_46);
x_48 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(x_15, x_32, x_25, x_47, x_11, x_14, x_12, x_10, x_9, x_44);
lean_dec(x_47);
lean_dec(x_32);
return x_48;
}
}
case 4:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_26);
lean_dec(x_25);
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_50, 0, x_32);
x_51 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_52 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_52);
x_53 = lean_mk_array(x_52, x_51);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_52, x_54);
lean_dec(x_52);
x_56 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_53, x_55);
x_57 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_49, x_56, x_33, x_50, x_14, x_12, x_10, x_9, x_29);
lean_dec(x_56);
lean_dec(x_49);
return x_57;
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_26);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_59, 0, x_32);
x_60 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_61 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_61);
x_62 = lean_mk_array(x_61, x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_61, x_63);
lean_dec(x_61);
x_65 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_62, x_64);
x_66 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_58, x_25, x_65, x_33, x_59, x_14, x_12, x_10, x_9, x_29);
lean_dec(x_65);
return x_66;
}
default: 
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_26, 0);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_26);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Environment_find_x3f(x_69, x_24, x_11);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_15);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed), 7, 1);
lean_closure_set(x_73, 0, x_15);
switch (lean_obj_tag(x_72)) {
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_73);
x_74 = l_Lean_ConstantInfo_name(x_72);
lean_inc(x_74);
x_75 = l_Lean_Meta_isAuxDef___redArg(x_74, x_9, x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_15);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l_Lean_Meta_recordUnfold___redArg(x_74, x_12, x_10, x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Expr_getAppNumArgs(x_15);
x_85 = lean_mk_empty_array_with_capacity(x_84);
lean_dec(x_84);
lean_inc(x_15);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_15, x_85);
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(x_15, x_72, x_25, x_86, x_11, x_14, x_12, x_10, x_9, x_83);
lean_dec(x_86);
lean_dec(x_72);
return x_87;
}
}
case 4:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_25);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_89, 0, x_72);
x_90 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_91 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_91);
x_92 = lean_mk_array(x_91, x_90);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_91, x_93);
lean_dec(x_91);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_92, x_94);
x_96 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_88, x_95, x_73, x_89, x_14, x_12, x_10, x_9, x_68);
lean_dec(x_95);
lean_dec(x_88);
return x_96;
}
case 7:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_72, 0);
lean_inc(x_97);
x_98 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed), 7, 1);
lean_closure_set(x_98, 0, x_72);
x_99 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_100 = l_Lean_Expr_getAppNumArgs(x_15);
lean_inc(x_100);
x_101 = lean_mk_array(x_100, x_99);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_100, x_102);
lean_dec(x_100);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_101, x_103);
x_105 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_97, x_25, x_104, x_73, x_98, x_14, x_12, x_10, x_9, x_68);
lean_dec(x_104);
return x_105;
}
default: 
{
lean_object* x_106; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_15);
lean_ctor_set(x_106, 1, x_68);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_107 = !lean_is_exclusive(x_18);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_18, 0);
lean_dec(x_108);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_18, 1);
lean_inc(x_109);
lean_dec(x_18);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
default: 
{
uint8_t x_111; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_111 = !lean_is_exclusive(x_18);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_18, 0);
lean_dec(x_112);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_18, 1);
lean_inc(x_113);
lean_dec(x_18);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_15);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_115 = !lean_is_exclusive(x_18);
if (x_115 == 0)
{
return x_18;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_18, 0);
x_117 = lean_ctor_get(x_18, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_18);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
block_137:
{
lean_object* x_129; lean_object* x_130; 
lean_inc(x_1);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(x_120, x_1, x_127, x_123, x_122, x_121, x_125);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_expr_eqv(x_126, x_120);
lean_dec(x_126);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = l_Lean_Expr_updateFn(x_1, x_120);
x_7 = x_131;
x_8 = x_120;
x_9 = x_121;
x_10 = x_122;
x_11 = x_128;
x_12 = x_123;
x_13 = x_124;
x_14 = x_127;
x_15 = x_133;
goto block_119;
}
else
{
x_7 = x_131;
x_8 = x_120;
x_9 = x_121;
x_10 = x_122;
x_11 = x_128;
x_12 = x_123;
x_13 = x_124;
x_14 = x_127;
x_15 = x_1;
goto block_119;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_1);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
lean_dec(x_130);
x_136 = l_Lean_Meta_whnfCore_go(x_135, x_127, x_123, x_122, x_121, x_134);
return x_136;
}
}
block_152:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_144 = l_Lean_Expr_getAppNumArgs(x_1);
x_145 = lean_mk_empty_array_with_capacity(x_144);
lean_dec(x_144);
x_146 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_145);
x_147 = lean_box(0);
x_148 = lean_unbox(x_147);
x_149 = lean_unbox(x_147);
x_150 = l_Lean_Expr_betaRev(x_138, x_146, x_148, x_149);
lean_dec(x_146);
x_151 = l_Lean_Meta_whnfCore_go(x_150, x_143, x_141, x_140, x_139, x_142);
return x_151;
}
block_162:
{
if (x_161 == 0)
{
x_120 = x_153;
x_121 = x_154;
x_122 = x_155;
x_123 = x_156;
x_124 = x_157;
x_125 = x_158;
x_126 = x_159;
x_127 = x_160;
x_128 = x_161;
goto block_137;
}
else
{
lean_dec(x_159);
lean_dec(x_157);
x_138 = x_153;
x_139 = x_154;
x_140 = x_155;
x_141 = x_156;
x_142 = x_158;
x_143 = x_160;
goto block_152;
}
}
block_177:
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_Expr_getAppFn(x_163);
lean_dec(x_163);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_170);
x_171 = l_Lean_Meta_whnfCore_go(x_170, x_165, x_166, x_167, x_168, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Expr_isLambda(x_172);
if (x_174 == 0)
{
x_153 = x_172;
x_154 = x_168;
x_155 = x_167;
x_156 = x_166;
x_157 = x_164;
x_158 = x_173;
x_159 = x_170;
x_160 = x_165;
x_161 = x_174;
goto block_162;
}
else
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_164, 13);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_isLambda(x_170);
if (x_176 == 0)
{
x_153 = x_172;
x_154 = x_168;
x_155 = x_167;
x_156 = x_166;
x_157 = x_164;
x_158 = x_173;
x_159 = x_170;
x_160 = x_165;
x_161 = x_174;
goto block_162;
}
else
{
x_120 = x_172;
x_121 = x_168;
x_122 = x_167;
x_123 = x_166;
x_124 = x_164;
x_125 = x_173;
x_126 = x_170;
x_127 = x_165;
x_128 = x_175;
goto block_137;
}
}
else
{
lean_dec(x_170);
lean_dec(x_164);
x_138 = x_172;
x_139 = x_168;
x_140 = x_167;
x_141 = x_166;
x_142 = x_173;
x_143 = x_165;
goto block_152;
}
}
}
else
{
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_1);
return x_171;
}
}
block_194:
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Meta_projectCore_x3f___redArg(x_179, x_178, x_183, x_184);
lean_dec(x_178);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
x_187 = !lean_is_exclusive(x_185);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_185, 0);
lean_dec(x_188);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_1);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_dec(x_185);
x_192 = lean_ctor_get(x_186, 0);
lean_inc(x_192);
lean_dec(x_186);
x_193 = l_Lean_Meta_whnfCore_go(x_192, x_180, x_181, x_182, x_183, x_191);
return x_193;
}
}
block_257:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_200; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
case 5:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_1, 0);
lean_inc(x_201);
x_202 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_203, 15);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_163 = x_201;
x_164 = x_203;
x_165 = x_195;
x_166 = x_196;
x_167 = x_197;
x_168 = x_198;
x_169 = x_205;
goto block_177;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
lean_dec(x_202);
lean_inc(x_1);
x_207 = l_Lean_Expr_letFunAppArgs_x3f(x_1);
if (lean_obj_tag(x_207) == 0)
{
x_163 = x_201;
x_164 = x_203;
x_165 = x_195;
x_166 = x_196;
x_167 = x_197;
x_168 = x_198;
x_169 = x_206;
goto block_177;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_1);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_216 = lean_array_push(x_215, x_213);
x_217 = l_Lean_Meta_expandLet(x_214, x_216);
x_218 = l_Lean_mkAppN(x_217, x_212);
lean_dec(x_212);
x_219 = l_Lean_Meta_whnfCore_go(x_218, x_195, x_196, x_197, x_198, x_206);
return x_219;
}
}
}
case 8:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_1, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_1, 3);
lean_inc(x_221);
x_222 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_223, 15);
lean_dec(x_223);
if (x_224 == 0)
{
uint8_t x_225; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_225 = !lean_is_exclusive(x_222);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_222, 0);
lean_dec(x_226);
lean_ctor_set(x_222, 0, x_1);
return x_222;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_dec(x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_1);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_1);
x_229 = lean_ctor_get(x_222, 1);
lean_inc(x_229);
lean_dec(x_222);
x_230 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_231 = lean_array_push(x_230, x_220);
x_232 = l_Lean_Meta_expandLet(x_221, x_231);
x_233 = l_Lean_Meta_whnfCore_go(x_232, x_195, x_196, x_197, x_198, x_229);
return x_233;
}
}
case 11:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_1, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 2);
lean_inc(x_235);
x_236 = l_Lean_Meta_getConfig___redArg(x_195, x_199);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get_uint8(x_237, 14);
lean_dec(x_237);
switch (x_238) {
case 0:
{
uint8_t x_239; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
x_239 = !lean_is_exclusive(x_236);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_236, 0);
lean_dec(x_240);
lean_ctor_set(x_236, 0, x_1);
return x_236;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
case 1:
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_244 = l_Lean_Meta_whnfCore_go(x_235, x_195, x_196, x_197, x_198, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_178 = x_234;
x_179 = x_245;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_246;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_244;
}
}
case 2:
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_236, 1);
lean_inc(x_247);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_248 = lean_whnf(x_235, x_195, x_196, x_197, x_198, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_178 = x_234;
x_179 = x_249;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_250;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_248;
}
}
default: 
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_236, 1);
lean_inc(x_251);
lean_dec(x_236);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_252 = l_Lean_Meta_whnfAtMostI(x_235, x_195, x_196, x_197, x_198, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_178 = x_234;
x_179 = x_253;
x_180 = x_195;
x_181 = x_196;
x_182 = x_197;
x_183 = x_198;
x_184 = x_254;
goto block_194;
}
else
{
lean_dec(x_234);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
return x_252;
}
}
}
}
default: 
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_1);
x_255 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3;
x_256 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_255, x_195, x_196, x_197, x_198, x_199);
return x_256;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_whnfCore_go_spec__0(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_whnfCore_go(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_12, x_11, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(1);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_13);
x_19 = lean_unbox(x_15);
x_20 = l_Lean_Meta_mkLambdaFVars(x_1, x_12, x_16, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_9, 0, x_22);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_9, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_9);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_box(0);
x_32 = lean_box(1);
x_33 = lean_box(1);
x_34 = lean_unbox(x_31);
x_35 = lean_unbox(x_32);
x_36 = lean_unbox(x_31);
x_37 = lean_unbox(x_33);
x_38 = l_Lean_Meta_mkLambdaFVars(x_1, x_30, x_34, x_35, x_36, x_37, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_expr_instantiate1(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_box(1);
x_17 = lean_box(1);
x_18 = lean_unbox(x_16);
x_19 = lean_unbox(x_17);
x_20 = l_Lean_Meta_mkLetFVars(x_15, x_13, x_18, x_19, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_20, 0, x_10);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_10, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_10);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0;
x_32 = lean_array_push(x_31, x_2);
x_33 = lean_box(1);
x_34 = lean_box(1);
x_35 = lean_unbox(x_33);
x_36 = lean_unbox(x_34);
x_37 = l_Lean_Meta_mkLetFVars(x_32, x_30, x_35, x_36, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_8, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = l_Lean_Expr_app___override(x_12, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Expr_app___override(x_12, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_25 = x_14;
} else {
 lean_dec_ref(x_14);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Expr_app___override(x_12, x_24);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
else
{
lean_dec(x_12);
return x_13;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__0), 7, 0);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg(x_1, x_29, x_31, x_2, x_3, x_4, x_5, x_6);
return x_32;
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_35, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1___boxed), 7, 1);
lean_closure_set(x_41, 0, x_36);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg(x_33, x_34, x_40, x_41, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
}
else
{
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
case 10:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = l_Lean_Meta_smartUnfoldingMatch_x3f(x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_inc(x_46);
x_48 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_46, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
return x_48;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ptr_addr(x_46);
lean_dec(x_46);
x_57 = lean_ptr_addr(x_55);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_1);
x_59 = l_Lean_Expr_mdata___override(x_45, x_55);
x_51 = x_59;
goto block_54;
}
else
{
lean_dec(x_55);
lean_dec(x_45);
x_51 = x_1;
goto block_54;
}
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
return x_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
lean_dec(x_47);
x_61 = l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(x_60, x_2, x_3, x_4, x_5, x_6);
return x_61;
}
}
case 11:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_inc(x_64);
x_65 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_64, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
return x_65;
}
else
{
lean_object* x_72; size_t x_73; size_t x_74; uint8_t x_75; 
lean_dec(x_65);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_74 = lean_ptr_addr(x_72);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_1);
x_76 = l_Lean_Expr_proj___override(x_62, x_63, x_72);
x_68 = x_76;
goto block_71;
}
else
{
lean_dec(x_72);
lean_dec(x_63);
lean_dec(x_62);
x_68 = x_1;
goto block_71;
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
return x_65;
}
}
default: 
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_6);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Meta_smartUnfoldingMatchAlt_x3f(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
x_14 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_12, x_2, x_3, x_4, x_5, x_10);
return x_14;
}
else
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_Meta_smartUnfoldingMatchAlt_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_16, x_2, x_3, x_4, x_5, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Meta_getStuckMVar_x3f(x_21, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = lean_synth_pending(x_31, x_2, x_3, x_4, x_5, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_6 = x_41;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_7, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_dec(x_7);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_withLetDecl___at___Lean_Meta_smartUnfoldingReduce_x3f_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_smartUnfoldingReduce_x3f_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static uint64_t _init_l_Lean_Meta_unfoldProjInst_x3f___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldProjInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_getStuckMVar_x3f_spec__0___redArg(x_12, x_5, x_6);
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
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_19;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
uint64_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint8_t x_60; lean_object* x_61; 
x_25 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = lean_ctor_get(x_2, 4);
x_31 = lean_ctor_get(x_2, 5);
x_32 = lean_ctor_get(x_2, 6);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_35 = lean_ctor_get_uint8(x_23, 0);
x_36 = lean_ctor_get_uint8(x_23, 1);
x_37 = lean_ctor_get_uint8(x_23, 2);
x_38 = lean_ctor_get_uint8(x_23, 3);
x_39 = lean_ctor_get_uint8(x_23, 4);
x_40 = lean_ctor_get_uint8(x_23, 5);
x_41 = lean_ctor_get_uint8(x_23, 6);
x_42 = lean_ctor_get_uint8(x_23, 7);
x_43 = lean_ctor_get_uint8(x_23, 8);
x_44 = lean_ctor_get_uint8(x_23, 10);
x_45 = lean_ctor_get_uint8(x_23, 11);
x_46 = lean_ctor_get_uint8(x_23, 12);
x_47 = lean_ctor_get_uint8(x_23, 13);
x_48 = lean_ctor_get_uint8(x_23, 14);
x_49 = lean_ctor_get_uint8(x_23, 15);
x_50 = lean_ctor_get_uint8(x_23, 16);
x_51 = lean_ctor_get_uint8(x_23, 17);
x_52 = lean_box(0);
x_53 = lean_box(1);
x_54 = lean_unbox(x_53);
lean_ctor_set_uint8(x_23, 9, x_54);
x_55 = 2;
x_56 = lean_uint64_shift_right(x_25, x_55);
x_57 = lean_uint64_shift_left(x_56, x_55);
x_58 = l_Lean_Meta_unfoldProjInst_x3f___closed__0;
x_59 = lean_uint64_lor(x_57, x_58);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_59);
x_60 = lean_unbox(x_52);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_60, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_7 = x_63;
goto block_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint64_t x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Expr_getAppFn(x_65);
x_67 = lean_box(3);
x_68 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_68, 0, x_35);
lean_ctor_set_uint8(x_68, 1, x_36);
lean_ctor_set_uint8(x_68, 2, x_37);
lean_ctor_set_uint8(x_68, 3, x_38);
lean_ctor_set_uint8(x_68, 4, x_39);
lean_ctor_set_uint8(x_68, 5, x_40);
lean_ctor_set_uint8(x_68, 6, x_41);
lean_ctor_set_uint8(x_68, 7, x_42);
lean_ctor_set_uint8(x_68, 8, x_43);
x_69 = lean_unbox(x_67);
lean_ctor_set_uint8(x_68, 9, x_69);
lean_ctor_set_uint8(x_68, 10, x_44);
lean_ctor_set_uint8(x_68, 11, x_45);
lean_ctor_set_uint8(x_68, 12, x_46);
lean_ctor_set_uint8(x_68, 13, x_47);
lean_ctor_set_uint8(x_68, 14, x_48);
lean_ctor_set_uint8(x_68, 15, x_49);
lean_ctor_set_uint8(x_68, 16, x_50);
lean_ctor_set_uint8(x_68, 17, x_51);
x_70 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_71 = lean_uint64_lor(x_57, x_70);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_72, 2, x_28);
lean_ctor_set(x_72, 3, x_29);
lean_ctor_set(x_72, 4, x_30);
lean_ctor_set(x_72, 5, x_31);
lean_ctor_set(x_72, 6, x_32);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_26);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_33);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_34);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_reduceProj_x3f(x_66, x_72, x_3, x_4, x_5, x_64);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_65);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_7 = x_75;
goto block_10;
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = l_Lean_Meta_recordUnfold___redArg(x_12, x_3, x_4, x_76);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_83 = l_Lean_Expr_getAppNumArgs(x_65);
lean_inc(x_83);
x_84 = lean_mk_array(x_83, x_82);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_83, x_85);
lean_dec(x_83);
x_87 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_65, x_84, x_86);
x_88 = l_Lean_mkAppN(x_78, x_87);
lean_dec(x_87);
x_89 = l_Lean_Expr_headBeta(x_88);
lean_ctor_set(x_74, 0, x_89);
lean_ctor_set(x_79, 0, x_74);
return x_79;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_dec(x_79);
x_91 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_92 = l_Lean_Expr_getAppNumArgs(x_65);
lean_inc(x_92);
x_93 = lean_mk_array(x_92, x_91);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_92, x_94);
lean_dec(x_92);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_65, x_93, x_95);
x_97 = l_Lean_mkAppN(x_78, x_96);
lean_dec(x_96);
x_98 = l_Lean_Expr_headBeta(x_97);
lean_ctor_set(x_74, 0, x_98);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_74);
lean_ctor_set(x_99, 1, x_90);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_74, 0);
lean_inc(x_100);
lean_dec(x_74);
x_101 = l_Lean_Meta_recordUnfold___redArg(x_12, x_3, x_4, x_76);
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_105 = l_Lean_Expr_getAppNumArgs(x_65);
lean_inc(x_105);
x_106 = lean_mk_array(x_105, x_104);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_sub(x_105, x_107);
lean_dec(x_105);
x_109 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_65, x_106, x_108);
x_110 = l_Lean_mkAppN(x_100, x_109);
lean_dec(x_109);
x_111 = l_Lean_Expr_headBeta(x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_102);
return x_113;
}
}
}
else
{
lean_dec(x_65);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_73;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
}
else
{
uint64_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint8_t x_150; lean_object* x_151; 
x_114 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_115 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_116 = lean_ctor_get(x_2, 1);
x_117 = lean_ctor_get(x_2, 2);
x_118 = lean_ctor_get(x_2, 3);
x_119 = lean_ctor_get(x_2, 4);
x_120 = lean_ctor_get(x_2, 5);
x_121 = lean_ctor_get(x_2, 6);
x_122 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_123 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_124 = lean_ctor_get_uint8(x_23, 0);
x_125 = lean_ctor_get_uint8(x_23, 1);
x_126 = lean_ctor_get_uint8(x_23, 2);
x_127 = lean_ctor_get_uint8(x_23, 3);
x_128 = lean_ctor_get_uint8(x_23, 4);
x_129 = lean_ctor_get_uint8(x_23, 5);
x_130 = lean_ctor_get_uint8(x_23, 6);
x_131 = lean_ctor_get_uint8(x_23, 7);
x_132 = lean_ctor_get_uint8(x_23, 8);
x_133 = lean_ctor_get_uint8(x_23, 10);
x_134 = lean_ctor_get_uint8(x_23, 11);
x_135 = lean_ctor_get_uint8(x_23, 12);
x_136 = lean_ctor_get_uint8(x_23, 13);
x_137 = lean_ctor_get_uint8(x_23, 14);
x_138 = lean_ctor_get_uint8(x_23, 15);
x_139 = lean_ctor_get_uint8(x_23, 16);
x_140 = lean_ctor_get_uint8(x_23, 17);
lean_dec(x_23);
x_141 = lean_box(0);
x_142 = lean_box(1);
x_143 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_143, 0, x_124);
lean_ctor_set_uint8(x_143, 1, x_125);
lean_ctor_set_uint8(x_143, 2, x_126);
lean_ctor_set_uint8(x_143, 3, x_127);
lean_ctor_set_uint8(x_143, 4, x_128);
lean_ctor_set_uint8(x_143, 5, x_129);
lean_ctor_set_uint8(x_143, 6, x_130);
lean_ctor_set_uint8(x_143, 7, x_131);
lean_ctor_set_uint8(x_143, 8, x_132);
x_144 = lean_unbox(x_142);
lean_ctor_set_uint8(x_143, 9, x_144);
lean_ctor_set_uint8(x_143, 10, x_133);
lean_ctor_set_uint8(x_143, 11, x_134);
lean_ctor_set_uint8(x_143, 12, x_135);
lean_ctor_set_uint8(x_143, 13, x_136);
lean_ctor_set_uint8(x_143, 14, x_137);
lean_ctor_set_uint8(x_143, 15, x_138);
lean_ctor_set_uint8(x_143, 16, x_139);
lean_ctor_set_uint8(x_143, 17, x_140);
x_145 = 2;
x_146 = lean_uint64_shift_right(x_114, x_145);
x_147 = lean_uint64_shift_left(x_146, x_145);
x_148 = l_Lean_Meta_unfoldProjInst_x3f___closed__0;
x_149 = lean_uint64_lor(x_147, x_148);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_ctor_set(x_2, 0, x_143);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_149);
x_150 = lean_unbox(x_141);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_151 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_150, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_7 = x_153;
goto block_10;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint64_t x_160; uint64_t x_161; lean_object* x_162; lean_object* x_163; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = l_Lean_Expr_getAppFn(x_155);
x_157 = lean_box(3);
x_158 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_158, 0, x_124);
lean_ctor_set_uint8(x_158, 1, x_125);
lean_ctor_set_uint8(x_158, 2, x_126);
lean_ctor_set_uint8(x_158, 3, x_127);
lean_ctor_set_uint8(x_158, 4, x_128);
lean_ctor_set_uint8(x_158, 5, x_129);
lean_ctor_set_uint8(x_158, 6, x_130);
lean_ctor_set_uint8(x_158, 7, x_131);
lean_ctor_set_uint8(x_158, 8, x_132);
x_159 = lean_unbox(x_157);
lean_ctor_set_uint8(x_158, 9, x_159);
lean_ctor_set_uint8(x_158, 10, x_133);
lean_ctor_set_uint8(x_158, 11, x_134);
lean_ctor_set_uint8(x_158, 12, x_135);
lean_ctor_set_uint8(x_158, 13, x_136);
lean_ctor_set_uint8(x_158, 14, x_137);
lean_ctor_set_uint8(x_158, 15, x_138);
lean_ctor_set_uint8(x_158, 16, x_139);
lean_ctor_set_uint8(x_158, 17, x_140);
x_160 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_161 = lean_uint64_lor(x_147, x_160);
x_162 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_116);
lean_ctor_set(x_162, 2, x_117);
lean_ctor_set(x_162, 3, x_118);
lean_ctor_set(x_162, 4, x_119);
lean_ctor_set(x_162, 5, x_120);
lean_ctor_set(x_162, 6, x_121);
lean_ctor_set_uint64(x_162, sizeof(void*)*7, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 8, x_115);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 9, x_122);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 10, x_123);
lean_inc(x_4);
lean_inc(x_3);
x_163 = l_Lean_Meta_reduceProj_x3f(x_156, x_162, x_3, x_4, x_5, x_154);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec(x_155);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_7 = x_165;
goto block_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Meta_recordUnfold___redArg(x_12, x_3, x_4, x_166);
lean_dec(x_4);
lean_dec(x_3);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_173 = l_Lean_Expr_getAppNumArgs(x_155);
lean_inc(x_173);
x_174 = lean_mk_array(x_173, x_172);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_sub(x_173, x_175);
lean_dec(x_173);
x_177 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_155, x_174, x_176);
x_178 = l_Lean_mkAppN(x_167, x_177);
lean_dec(x_177);
x_179 = l_Lean_Expr_headBeta(x_178);
if (lean_is_scalar(x_168)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_168;
}
lean_ctor_set(x_180, 0, x_179);
if (lean_is_scalar(x_171)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_171;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_170);
return x_181;
}
}
else
{
lean_dec(x_155);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_163;
}
}
}
else
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_151;
}
}
}
else
{
lean_object* x_182; uint64_t x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; 
x_182 = lean_ctor_get(x_2, 0);
x_183 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_184 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_185 = lean_ctor_get(x_2, 1);
x_186 = lean_ctor_get(x_2, 2);
x_187 = lean_ctor_get(x_2, 3);
x_188 = lean_ctor_get(x_2, 4);
x_189 = lean_ctor_get(x_2, 5);
x_190 = lean_ctor_get(x_2, 6);
x_191 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_192 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_182);
lean_dec(x_2);
x_193 = lean_ctor_get_uint8(x_182, 0);
x_194 = lean_ctor_get_uint8(x_182, 1);
x_195 = lean_ctor_get_uint8(x_182, 2);
x_196 = lean_ctor_get_uint8(x_182, 3);
x_197 = lean_ctor_get_uint8(x_182, 4);
x_198 = lean_ctor_get_uint8(x_182, 5);
x_199 = lean_ctor_get_uint8(x_182, 6);
x_200 = lean_ctor_get_uint8(x_182, 7);
x_201 = lean_ctor_get_uint8(x_182, 8);
x_202 = lean_ctor_get_uint8(x_182, 10);
x_203 = lean_ctor_get_uint8(x_182, 11);
x_204 = lean_ctor_get_uint8(x_182, 12);
x_205 = lean_ctor_get_uint8(x_182, 13);
x_206 = lean_ctor_get_uint8(x_182, 14);
x_207 = lean_ctor_get_uint8(x_182, 15);
x_208 = lean_ctor_get_uint8(x_182, 16);
x_209 = lean_ctor_get_uint8(x_182, 17);
if (lean_is_exclusive(x_182)) {
 x_210 = x_182;
} else {
 lean_dec_ref(x_182);
 x_210 = lean_box(0);
}
x_211 = lean_box(0);
x_212 = lean_box(1);
if (lean_is_scalar(x_210)) {
 x_213 = lean_alloc_ctor(0, 0, 18);
} else {
 x_213 = x_210;
}
lean_ctor_set_uint8(x_213, 0, x_193);
lean_ctor_set_uint8(x_213, 1, x_194);
lean_ctor_set_uint8(x_213, 2, x_195);
lean_ctor_set_uint8(x_213, 3, x_196);
lean_ctor_set_uint8(x_213, 4, x_197);
lean_ctor_set_uint8(x_213, 5, x_198);
lean_ctor_set_uint8(x_213, 6, x_199);
lean_ctor_set_uint8(x_213, 7, x_200);
lean_ctor_set_uint8(x_213, 8, x_201);
x_214 = lean_unbox(x_212);
lean_ctor_set_uint8(x_213, 9, x_214);
lean_ctor_set_uint8(x_213, 10, x_202);
lean_ctor_set_uint8(x_213, 11, x_203);
lean_ctor_set_uint8(x_213, 12, x_204);
lean_ctor_set_uint8(x_213, 13, x_205);
lean_ctor_set_uint8(x_213, 14, x_206);
lean_ctor_set_uint8(x_213, 15, x_207);
lean_ctor_set_uint8(x_213, 16, x_208);
lean_ctor_set_uint8(x_213, 17, x_209);
x_215 = 2;
x_216 = lean_uint64_shift_right(x_183, x_215);
x_217 = lean_uint64_shift_left(x_216, x_215);
x_218 = l_Lean_Meta_unfoldProjInst_x3f___closed__0;
x_219 = lean_uint64_lor(x_217, x_218);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_220 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_185);
lean_ctor_set(x_220, 2, x_186);
lean_ctor_set(x_220, 3, x_187);
lean_ctor_set(x_220, 4, x_188);
lean_ctor_set(x_220, 5, x_189);
lean_ctor_set(x_220, 6, x_190);
lean_ctor_set_uint64(x_220, sizeof(void*)*7, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 8, x_184);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 9, x_191);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 10, x_192);
x_221 = lean_unbox(x_211);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_222 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_221, x_220, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_7 = x_224;
goto block_10;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint64_t x_231; uint64_t x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
lean_dec(x_223);
x_227 = l_Lean_Expr_getAppFn(x_226);
x_228 = lean_box(3);
x_229 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_229, 0, x_193);
lean_ctor_set_uint8(x_229, 1, x_194);
lean_ctor_set_uint8(x_229, 2, x_195);
lean_ctor_set_uint8(x_229, 3, x_196);
lean_ctor_set_uint8(x_229, 4, x_197);
lean_ctor_set_uint8(x_229, 5, x_198);
lean_ctor_set_uint8(x_229, 6, x_199);
lean_ctor_set_uint8(x_229, 7, x_200);
lean_ctor_set_uint8(x_229, 8, x_201);
x_230 = lean_unbox(x_228);
lean_ctor_set_uint8(x_229, 9, x_230);
lean_ctor_set_uint8(x_229, 10, x_202);
lean_ctor_set_uint8(x_229, 11, x_203);
lean_ctor_set_uint8(x_229, 12, x_204);
lean_ctor_set_uint8(x_229, 13, x_205);
lean_ctor_set_uint8(x_229, 14, x_206);
lean_ctor_set_uint8(x_229, 15, x_207);
lean_ctor_set_uint8(x_229, 16, x_208);
lean_ctor_set_uint8(x_229, 17, x_209);
x_231 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1;
x_232 = lean_uint64_lor(x_217, x_231);
x_233 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_185);
lean_ctor_set(x_233, 2, x_186);
lean_ctor_set(x_233, 3, x_187);
lean_ctor_set(x_233, 4, x_188);
lean_ctor_set(x_233, 5, x_189);
lean_ctor_set(x_233, 6, x_190);
lean_ctor_set_uint64(x_233, sizeof(void*)*7, x_232);
lean_ctor_set_uint8(x_233, sizeof(void*)*7 + 8, x_184);
lean_ctor_set_uint8(x_233, sizeof(void*)*7 + 9, x_191);
lean_ctor_set_uint8(x_233, sizeof(void*)*7 + 10, x_192);
lean_inc(x_4);
lean_inc(x_3);
x_234 = l_Lean_Meta_reduceProj_x3f(x_227, x_233, x_3, x_4, x_5, x_225);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
lean_dec(x_226);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_7 = x_236;
goto block_10;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_239 = x_235;
} else {
 lean_dec_ref(x_235);
 x_239 = lean_box(0);
}
x_240 = l_Lean_Meta_recordUnfold___redArg(x_12, x_3, x_4, x_237);
lean_dec(x_4);
lean_dec(x_3);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
x_243 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_244 = l_Lean_Expr_getAppNumArgs(x_226);
lean_inc(x_244);
x_245 = lean_mk_array(x_244, x_243);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_sub(x_244, x_246);
lean_dec(x_244);
x_248 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_226, x_245, x_247);
x_249 = l_Lean_mkAppN(x_238, x_248);
lean_dec(x_248);
x_250 = l_Lean_Expr_headBeta(x_249);
if (lean_is_scalar(x_239)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_239;
}
lean_ctor_set(x_251, 0, x_250);
if (lean_is_scalar(x_242)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_242;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_241);
return x_252;
}
}
else
{
lean_dec(x_226);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_234;
}
}
}
else
{
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_222;
}
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_6);
return x_254;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_ConstantInfo_levelParams(x_2);
x_9 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
x_10 = l_List_lengthTR___redArg(x_3);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Core_instantiateValueLevelParams(x_2, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_recordUnfold___redArg(x_1, x_4, x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_ConstantInfo_levelParams(x_1);
x_9 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
x_10 = l_List_lengthTR___redArg(x_2);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Expr_betaRev(x_16, x_3, x_18, x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Expr_betaRev(x_21, x_3, x_24, x_4);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_ConstantInfo_levelParams(x_4);
x_14 = l_List_lengthTR___redArg(x_13);
lean_dec(x_13);
x_15 = l_List_lengthTR___redArg(x_5);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Core_instantiateValueLevelParams(x_4, x_5, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Expr_betaRev(x_20, x_6, x_23, x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_24, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_28);
x_29 = lean_get_structural_rec_arg_pos(x_28, x_10, x_11, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_8);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_recordUnfold___redArg(x_28, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_26);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = l_Lean_Expr_getAppNumArgs(x_2);
x_42 = lean_nat_dec_le(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_29);
x_43 = lean_nat_sub(x_41, x_40);
lean_dec(x_40);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
lean_dec(x_43);
x_46 = l_Lean_Expr_getRevArg_x21(x_2, x_45);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher(x_46, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_10);
lean_inc(x_9);
x_50 = l_Lean_Meta_isConstructorApp(x_48, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_60; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_60 = lean_unbox(x_52);
lean_dec(x_52);
if (x_60 == 0)
{
if (x_3 == 0)
{
lean_free_object(x_50);
goto block_59;
}
else
{
lean_object* x_61; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_61 = lean_box(0);
lean_ctor_set(x_50, 0, x_61);
return x_50;
}
}
else
{
lean_free_object(x_50);
goto block_59;
}
block_59:
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Meta_recordUnfold___redArg(x_28, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_26);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_69; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_69 = lean_unbox(x_62);
lean_dec(x_62);
if (x_69 == 0)
{
if (x_3 == 0)
{
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_63);
return x_71;
}
}
else
{
goto block_68;
}
block_68:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = l_Lean_Meta_recordUnfold___redArg(x_28, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_26);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_72 = !lean_is_exclusive(x_50);
if (x_72 == 0)
{
return x_50;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_50, 0);
x_74 = lean_ctor_get(x_50, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_50);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_47);
if (x_76 == 0)
{
return x_47;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_47, 0);
x_78 = lean_ctor_get(x_47, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_47);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = lean_box(0);
lean_ctor_set(x_29, 0, x_80);
return x_29;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_29, 1);
lean_inc(x_81);
lean_dec(x_29);
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
lean_dec(x_30);
x_83 = l_Lean_Expr_getAppNumArgs(x_2);
x_84 = lean_nat_dec_le(x_83, x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_nat_sub(x_83, x_82);
lean_dec(x_82);
lean_dec(x_83);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_85, x_86);
lean_dec(x_85);
x_88 = l_Lean_Expr_getRevArg_x21(x_2, x_87);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_89 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher(x_88, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_10);
lean_inc(x_9);
x_92 = l_Lean_Meta_isConstructorApp(x_90, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_101; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_101 = lean_unbox(x_93);
lean_dec(x_93);
if (x_101 == 0)
{
if (x_3 == 0)
{
lean_dec(x_95);
goto block_100;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_102 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_94);
return x_103;
}
}
else
{
lean_dec(x_95);
goto block_100;
}
block_100:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = l_Lean_Meta_recordUnfold___redArg(x_28, x_9, x_10, x_94);
lean_dec(x_10);
lean_dec(x_9);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_26);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_106 = x_92;
} else {
 lean_dec_ref(x_92);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_108 = lean_ctor_get(x_89, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_89, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_110 = x_89;
} else {
 lean_dec_ref(x_89);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_81);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_114 = !lean_is_exclusive(x_29);
if (x_114 == 0)
{
return x_29;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_29, 0);
x_116 = lean_ctor_get(x_29, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_29);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
}
else
{
uint8_t x_118; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_118 = !lean_is_exclusive(x_19);
if (x_118 == 0)
{
return x_19;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_19, 0);
x_120 = lean_ctor_get(x_19, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_19);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_ConstantInfo_hasValue(x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_ConstantInfo_name(x_1);
x_15 = l_Lean_Meta_recordUnfold___redArg(x_14, x_7, x_8, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Expr_getAppNumArgs(x_3);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_3, x_18);
x_20 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg(x_1, x_4, x_19, x_2, x_8, x_9, x_16);
lean_dec(x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfoNoEx_x3f___redArg(x_8, x_2, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_st_ref_get(x_6, x_18);
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
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
x_33 = l_Lean_Meta_unfoldDefinition_x3f___closed__0;
x_34 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec(x_21);
x_24 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
lean_inc(x_8);
x_37 = l_Lean_Name_str___override(x_8, x_36);
x_38 = l_Lean_Environment_contains(x_35, x_37, x_34);
x_24 = x_38;
goto block_31;
}
block_31:
{
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_ConstantInfo_hasValue(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_23);
x_28 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg(x_8, x_19, x_9, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
case 5:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = l_Lean_Expr_getAppFn(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 4)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_47 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getConstInfo_x3f(x_45, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_unfoldProjInstWhenInstances_x3f(x_1, x_3, x_4, x_5, x_6, x_49);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lean_ConstantInfo_levelParams(x_54);
x_56 = l_List_lengthTR___redArg(x_55);
lean_dec(x_55);
x_57 = l_List_lengthTR___redArg(x_46);
x_58 = lean_nat_dec_eq(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
lean_ctor_set(x_47, 0, x_59);
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_47);
x_60 = lean_ctor_get(x_5, 2);
lean_inc(x_60);
x_61 = lean_box(0);
x_71 = l_Lean_Meta_unfoldDefinition_x3f___closed__0;
x_72 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_60, x_71);
lean_dec(x_60);
if (x_72 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_90 = lean_box(0);
x_91 = lean_unbox(x_61);
x_92 = l_Lean_Meta_unfoldDefinition_x3f___lam__0(x_54, x_91, x_1, x_46, x_90, x_3, x_4, x_5, x_6, x_52);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_54);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_st_ref_get(x_6, x_52);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_ConstantInfo_name(x_54);
x_98 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
x_99 = l_Lean_Name_str___override(x_97, x_98);
x_100 = l_Lean_Environment_find_x3f(x_96, x_99, x_58);
if (lean_obj_tag(x_100) == 0)
{
x_73 = x_3;
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_95;
goto block_89;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = l_Lean_Expr_getAppNumArgs(x_1);
x_103 = lean_mk_empty_array_with_capacity(x_102);
lean_dec(x_102);
lean_inc(x_1);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_103);
x_105 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2(x_54, x_1, x_72, x_101, x_46, x_104, x_58, x_3, x_4, x_5, x_6, x_95);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_1);
lean_dec(x_54);
return x_105;
}
else
{
lean_dec(x_101);
x_73 = x_3;
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_95;
goto block_89;
}
}
}
block_70:
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = lean_box(0);
x_68 = lean_unbox(x_61);
x_69 = l_Lean_Meta_unfoldDefinition_x3f___lam__0(x_54, x_68, x_1, x_46, x_67, x_64, x_62, x_66, x_63, x_65);
lean_dec(x_63);
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_64);
lean_dec(x_54);
return x_69;
}
block_89:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Lean_ConstantInfo_name(x_54);
x_79 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_78, x_76, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_62 = x_74;
x_63 = x_76;
x_64 = x_73;
x_65 = x_81;
x_66 = x_75;
goto block_70;
}
else
{
lean_dec(x_80);
if (x_72 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_62 = x_74;
x_63 = x_76;
x_64 = x_73;
x_65 = x_82;
x_66 = x_75;
goto block_70;
}
else
{
uint8_t x_83; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_79, 0, x_85);
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
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
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_47, 1);
lean_inc(x_106);
lean_dec(x_47);
x_107 = lean_ctor_get(x_48, 0);
lean_inc(x_107);
lean_dec(x_48);
x_108 = l_Lean_ConstantInfo_levelParams(x_107);
x_109 = l_List_lengthTR___redArg(x_108);
lean_dec(x_108);
x_110 = l_List_lengthTR___redArg(x_46);
x_111 = lean_nat_dec_eq(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_114 = lean_ctor_get(x_5, 2);
lean_inc(x_114);
x_115 = lean_box(0);
x_125 = l_Lean_Meta_unfoldDefinition_x3f___closed__0;
x_126 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_114, x_125);
lean_dec(x_114);
if (x_126 == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_142 = lean_box(0);
x_143 = lean_unbox(x_115);
x_144 = l_Lean_Meta_unfoldDefinition_x3f___lam__0(x_107, x_143, x_1, x_46, x_142, x_3, x_4, x_5, x_6, x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_107);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_st_ref_get(x_6, x_106);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_ConstantInfo_name(x_107);
x_150 = l_Lean_Meta_smartUnfoldingSuffix___closed__0;
x_151 = l_Lean_Name_str___override(x_149, x_150);
x_152 = l_Lean_Environment_find_x3f(x_148, x_151, x_111);
if (lean_obj_tag(x_152) == 0)
{
x_127 = x_3;
x_128 = x_4;
x_129 = x_5;
x_130 = x_6;
x_131 = x_147;
goto block_141;
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = l_Lean_Expr_getAppNumArgs(x_1);
x_155 = lean_mk_empty_array_with_capacity(x_154);
lean_dec(x_154);
lean_inc(x_1);
x_156 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_155);
x_157 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2(x_107, x_1, x_126, x_153, x_46, x_156, x_111, x_3, x_4, x_5, x_6, x_147);
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_1);
lean_dec(x_107);
return x_157;
}
else
{
lean_dec(x_153);
x_127 = x_3;
x_128 = x_4;
x_129 = x_5;
x_130 = x_6;
x_131 = x_147;
goto block_141;
}
}
}
block_124:
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_121 = lean_box(0);
x_122 = lean_unbox(x_115);
x_123 = l_Lean_Meta_unfoldDefinition_x3f___lam__0(x_107, x_122, x_1, x_46, x_121, x_118, x_116, x_120, x_117, x_119);
lean_dec(x_117);
lean_dec(x_120);
lean_dec(x_116);
lean_dec(x_118);
lean_dec(x_107);
return x_123;
}
block_141:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = l_Lean_ConstantInfo_name(x_107);
x_133 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_132, x_130, x_131);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_116 = x_128;
x_117 = x_130;
x_118 = x_127;
x_119 = x_135;
x_120 = x_129;
goto block_124;
}
else
{
lean_dec(x_134);
if (x_126 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_116 = x_128;
x_117 = x_130;
x_118 = x_127;
x_119 = x_136;
x_120 = x_129;
goto block_124;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_107);
lean_dec(x_46);
lean_dec(x_1);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_47);
if (x_158 == 0)
{
return x_47;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_47, 0);
x_160 = lean_ctor_get(x_47, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_47);
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
lean_dec(x_44);
x_162 = l_Lean_Meta_unfoldProjInstWhenInstances_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
return x_162;
}
}
default: 
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_7);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldProjInstWhenInstances_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getTransparency___redArg(x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_box(3);
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; 
lean_free_object(x_7);
x_16 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_10);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_box(3);
x_20 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = lean_unbox(x_19);
x_22 = l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_18);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___redArg(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_unfoldDefinition_x3f_spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_unfoldDefinition_x3f___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to unfold definition", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfoldDefinition___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_unfoldDefinition___closed__1;
x_13 = l_Lean_indentExpr(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_unfoldDefinition___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnfCore_go(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_21 = l_Lean_Meta_unfoldDefinition_x3f(x_9, x_20, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Meta_whnfHeadPred(x_28, x_1, x_3, x_4, x_5, x_6, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred___lam__0), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_whnfEasyCases(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_Meta_whnfEasyCases___closed__10;
x_10 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_11);
x_12 = l_Lean_FVarId_getDecl___redArg(x_11, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = l_Lean_Meta_getConfig___redArg(x_4, x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_56; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_56 = l_Lean_LocalDecl_isImplementationDetail(x_13);
lean_dec(x_13);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_22, 16);
lean_dec(x_22);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_59, x_11);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_dec(x_60);
lean_free_object(x_20);
lean_dec(x_3);
x_24 = x_4;
x_25 = x_58;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
goto block_49;
}
}
else
{
lean_free_object(x_20);
lean_dec(x_3);
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
goto block_55;
}
}
else
{
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_3);
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
goto block_55;
}
block_49:
{
if (x_25 == 0)
{
lean_dec(x_11);
x_3 = x_19;
x_4 = x_24;
x_5 = x_26;
x_6 = x_27;
x_7 = x_28;
x_8 = x_23;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_st_ref_take(x_26, x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_31, 2);
x_35 = l_Lean_FVarIdSet_insert(x_34, x_11);
lean_ctor_set(x_31, 2, x_35);
x_36 = lean_st_ref_set(x_26, x_31, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_19;
x_4 = x_24;
x_5 = x_26;
x_6 = x_27;
x_7 = x_28;
x_8 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
x_41 = lean_ctor_get(x_31, 2);
x_42 = lean_ctor_get(x_31, 3);
x_43 = lean_ctor_get(x_31, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_44 = l_Lean_FVarIdSet_insert(x_41, x_11);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_st_ref_set(x_26, x_45, x_32);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_3 = x_19;
x_4 = x_24;
x_5 = x_26;
x_6 = x_27;
x_7 = x_28;
x_8 = x_47;
goto _start;
}
}
}
block_55:
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_50, sizeof(void*)*7 + 8);
x_24 = x_50;
x_25 = x_54;
x_26 = x_51;
x_27 = x_52;
x_28 = x_53;
goto block_49;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_90; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_90 = l_Lean_LocalDecl_isImplementationDetail(x_13);
lean_dec(x_13);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_61, 16);
lean_dec(x_61);
if (x_91 == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
x_94 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_93, x_11);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_3);
lean_ctor_set(x_95, 1, x_62);
return x_95;
}
else
{
lean_dec(x_94);
lean_dec(x_3);
x_63 = x_4;
x_64 = x_92;
x_65 = x_5;
x_66 = x_6;
x_67 = x_7;
goto block_83;
}
}
else
{
lean_dec(x_3);
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
goto block_89;
}
}
else
{
lean_dec(x_61);
lean_dec(x_3);
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
goto block_89;
}
block_83:
{
if (x_64 == 0)
{
lean_dec(x_11);
x_3 = x_19;
x_4 = x_63;
x_5 = x_65;
x_6 = x_66;
x_7 = x_67;
x_8 = x_62;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_69 = lean_st_ref_take(x_65, x_62);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 4);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
x_78 = l_Lean_FVarIdSet_insert(x_74, x_11);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 5, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_73);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_75);
lean_ctor_set(x_79, 4, x_76);
x_80 = lean_st_ref_set(x_65, x_79, x_71);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_3 = x_19;
x_4 = x_63;
x_5 = x_65;
x_6 = x_66;
x_7 = x_67;
x_8 = x_81;
goto _start;
}
}
block_89:
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_84, sizeof(void*)*7 + 8);
x_63 = x_84;
x_64 = x_88;
x_65 = x_85;
x_66 = x_86;
x_67 = x_87;
goto block_83;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
case 2:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 0);
lean_inc(x_100);
x_101 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(x_100, x_5, x_8);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_101, 0);
lean_dec(x_104);
lean_ctor_set(x_101, 0, x_3);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_3);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
lean_dec(x_102);
x_3 = x_108;
x_8 = x_107;
goto _start;
}
}
case 3:
{
lean_object* x_110; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_3);
lean_ctor_set(x_110, 1, x_8);
return x_110;
}
case 6:
{
lean_object* x_111; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_8);
return x_111;
}
case 7:
{
lean_object* x_112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_8);
return x_112;
}
case 9:
{
lean_object* x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_8);
return x_113;
}
case 10:
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_3, 1);
lean_inc(x_114);
lean_dec(x_3);
x_3 = x_114;
goto _start;
}
default: 
{
lean_object* x_116; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_116 = l_Lean_Meta_whnfCore_go(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_117);
x_119 = lean_apply_6(x_1, x_117, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_127 = lean_box(0);
x_128 = lean_unbox(x_127);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_117);
x_129 = l_Lean_Meta_unfoldDefinition_x3f(x_117, x_128, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
lean_ctor_set(x_129, 0, x_117);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_117);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_117);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_dec(x_129);
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
lean_dec(x_130);
x_137 = l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0(x_2, x_136, x_4, x_5, x_6, x_7, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_129);
if (x_138 == 0)
{
return x_129;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_129, 0);
x_140 = lean_ctor_get(x_129, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_129);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_119);
if (x_142 == 0)
{
return x_119;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_119, 0);
x_144 = lean_ctor_get(x_119, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_119);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0_spec__0(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_2);
lean_dec(x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Expr_isAppOf(x_14, x_2);
lean_dec(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPred___at___Lean_Meta_whnfUntil_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_ConstantInfo_levelParams(x_2);
x_11 = l_List_lengthTR___redArg(x_10);
lean_dec(x_10);
x_12 = l_List_lengthTR___redArg(x_3);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Core_instantiateValueLevelParams(x_2, x_3, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_recordUnfold___redArg(x_1, x_6, x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Expr_betaRev(x_17, x_4, x_23, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_Expr_betaRev(x_17, x_4, x_28, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_ConstantInfo_name(x_1);
x_9 = l_Lean_Meta_recordUnfold___redArg(x_8, x_4, x_5, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isApp(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_ctor_set_tag(x_11, 1);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_19 = x_11;
} else {
 lean_dec_ref(x_11);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(1, 1, 0);
} else {
 x_20 = x_19;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_5, x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Environment_find_x3f(x_32, x_26, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_28, 0, x_36);
return x_28;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
switch (lean_obj_tag(x_37)) {
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_free_object(x_28);
lean_dec(x_2);
x_38 = l_Lean_ConstantInfo_name(x_37);
lean_inc(x_38);
x_39 = l_Lean_Meta_isAuxDef___redArg(x_38, x_5, x_31);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_Lean_Expr_getAppNumArgs(x_1);
x_50 = lean_mk_empty_array_with_capacity(x_49);
lean_dec(x_49);
x_51 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_50);
x_52 = lean_unbox(x_33);
x_53 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(x_38, x_37, x_27, x_51, x_52, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_51);
lean_dec(x_37);
return x_53;
}
}
case 4:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_28);
lean_dec(x_27);
x_54 = lean_ctor_get(x_37, 0);
lean_inc(x_54);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_56, 0, x_37);
x_57 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_58 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_58);
x_59 = lean_mk_array(x_58, x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_58, x_60);
lean_dec(x_58);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_59, x_61);
x_63 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_54, x_62, x_55, x_56, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_62);
lean_dec(x_54);
return x_63;
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_28);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_66, 0, x_37);
x_67 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_68 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_68, x_70);
lean_dec(x_68);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_69, x_71);
x_73 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_64, x_27, x_72, x_65, x_66, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_72);
return x_73;
}
default: 
{
lean_object* x_74; 
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_box(0);
lean_ctor_set(x_28, 0, x_74);
return x_28;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_28, 0);
x_76 = lean_ctor_get(x_28, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_28);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_box(0);
x_79 = lean_unbox(x_78);
x_80 = l_Lean_Environment_find_x3f(x_77, x_26, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
switch (lean_obj_tag(x_83)) {
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_2);
x_84 = l_Lean_ConstantInfo_name(x_83);
lean_inc(x_84);
x_85 = l_Lean_Meta_isAuxDef___redArg(x_84, x_5, x_76);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_Expr_getAppNumArgs(x_1);
x_94 = lean_mk_empty_array_with_capacity(x_93);
lean_dec(x_93);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_94);
x_96 = lean_unbox(x_78);
x_97 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(x_84, x_83, x_27, x_95, x_96, x_3, x_4, x_5, x_92);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_95);
lean_dec(x_83);
return x_97;
}
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_27);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_100 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_100, 0, x_83);
x_101 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_102 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_102);
x_103 = lean_mk_array(x_102, x_101);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_102, x_104);
lean_dec(x_102);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_105);
x_107 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_98, x_106, x_99, x_100, x_2, x_3, x_4, x_5, x_76);
lean_dec(x_106);
lean_dec(x_98);
return x_107;
}
case 7:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_83, 0);
lean_inc(x_108);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_110 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_110, 0, x_83);
x_111 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_112 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_112);
x_113 = lean_mk_array(x_112, x_111);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_sub(x_112, x_114);
lean_dec(x_112);
x_116 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_113, x_115);
x_117 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_108, x_27, x_116, x_109, x_110, x_2, x_3, x_4, x_5, x_76);
lean_dec(x_116);
return x_117;
}
default: 
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_83);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_76);
return x_119;
}
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_box(0);
lean_ctor_set(x_10, 0, x_120);
return x_10;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_10, 1);
lean_inc(x_121);
lean_dec(x_10);
x_122 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_122) == 4)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_5, x_121);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_box(0);
x_131 = lean_unbox(x_130);
x_132 = l_Lean_Environment_find_x3f(x_129, x_123, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_127);
return x_134;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec(x_132);
switch (lean_obj_tag(x_135)) {
case 1:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_128);
lean_dec(x_2);
x_136 = l_Lean_ConstantInfo_name(x_135);
lean_inc(x_136);
x_137 = l_Lean_Meta_isAuxDef___redArg(x_136, x_5, x_127);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_dec(x_137);
x_145 = l_Lean_Expr_getAppNumArgs(x_1);
x_146 = lean_mk_empty_array_with_capacity(x_145);
lean_dec(x_145);
x_147 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_146);
x_148 = lean_unbox(x_130);
x_149 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(x_136, x_135, x_124, x_147, x_148, x_3, x_4, x_5, x_144);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_147);
lean_dec(x_135);
return x_149;
}
}
case 4:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_128);
lean_dec(x_124);
x_150 = lean_ctor_get(x_135, 0);
lean_inc(x_150);
x_151 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_152 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_152, 0, x_135);
x_153 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_154 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_154);
x_155 = lean_mk_array(x_154, x_153);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_154, x_156);
lean_dec(x_154);
x_158 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_155, x_157);
x_159 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___redArg(x_150, x_158, x_151, x_152, x_2, x_3, x_4, x_5, x_127);
lean_dec(x_158);
lean_dec(x_150);
return x_159;
}
case 7:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_128);
x_160 = lean_ctor_get(x_135, 0);
lean_inc(x_160);
x_161 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed), 6, 0);
x_162 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed), 7, 1);
lean_closure_set(x_162, 0, x_135);
x_163 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0;
x_164 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_164);
x_165 = lean_mk_array(x_164, x_163);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_164, x_166);
lean_dec(x_164);
x_168 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_165, x_167);
x_169 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg(x_160, x_124, x_168, x_161, x_162, x_2, x_3, x_4, x_5, x_127);
lean_dec(x_168);
return x_169;
}
default: 
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_135);
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_128;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_127);
return x_171;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_122);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_121);
return x_173;
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_10);
if (x_174 == 0)
{
return x_10;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_10, 0);
x_176 = lean_ctor_get(x_10, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_10);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___Lean_Meta_reduceRecMatcher_x3f_spec__0(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceRecMatcher_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceRecMatcher_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = lean_ctor_get(x_5, 2);
x_13 = l_Lean_Environment_evalConstCheck___redArg(x_11, x_12, x_1, x_2);
x_14 = l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__1;
x_8 = l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceBoolNativeUnsafe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_reduceNatNativeUnsafe___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_reduceNatNativeUnsafe___closed__0;
x_8 = l_Lean_evalConstCheck___at___Lean_Meta_reduceBoolNativeUnsafe_spec__0___redArg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceNatNativeUnsafe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBool", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__0;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__4;
x_2 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__7;
x_2 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_reduceNative_x3f___closed__1;
x_16 = lean_name_eq(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_reduceNative_x3f___closed__3;
x_18 = lean_name_eq(x_13, x_17);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Meta_reduceNatNativeUnsafe(x_14, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_mkNatLit(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Lean_mkNatLit(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_13);
x_35 = l_Lean_Meta_reduceBoolNativeUnsafe(x_14, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
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
x_43 = lean_unbox(x_36);
lean_dec(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Meta_reduceNative_x3f___closed__6;
x_39 = x_44;
goto block_42;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Meta_reduceNative_x3f___closed__9;
x_39 = x_45;
goto block_42;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
x_7 = x_6;
goto block_10;
}
}
else
{
lean_dec(x_11);
lean_dec(x_1);
x_7 = x_6;
goto block_10;
}
}
else
{
lean_dec(x_1);
x_7 = x_6;
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceNative_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_withNatValue___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Meta_whnfEasyCases___closed__1;
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 2);
x_52 = lean_ctor_get(x_47, 3);
x_53 = lean_ctor_get(x_47, 4);
x_54 = lean_ctor_get(x_47, 1);
lean_dec(x_54);
x_55 = l_Lean_Meta_whnfEasyCases___closed__2;
x_56 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_53);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_61, 0, x_52);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_62, 0, x_51);
lean_ctor_set(x_47, 4, x_60);
lean_ctor_set(x_47, 3, x_61);
lean_ctor_set(x_47, 2, x_62);
lean_ctor_set(x_47, 1, x_55);
lean_ctor_set(x_47, 0, x_59);
lean_ctor_set(x_45, 1, x_56);
x_63 = l_ReaderT_instMonad___redArg(x_45);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_93; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 2);
x_70 = lean_ctor_get(x_65, 3);
x_71 = lean_ctor_get(x_65, 4);
x_72 = lean_ctor_get(x_65, 1);
lean_dec(x_72);
x_73 = l_Lean_Meta_whnfEasyCases___closed__4;
x_74 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_68);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_75, 0, x_68);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_68);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_78, 0, x_71);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_79, 0, x_70);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_80, 0, x_69);
lean_ctor_set(x_65, 4, x_78);
lean_ctor_set(x_65, 3, x_79);
lean_ctor_set(x_65, 2, x_80);
lean_ctor_set(x_65, 1, x_73);
lean_ctor_set(x_65, 0, x_77);
lean_ctor_set(x_63, 1, x_74);
x_81 = l_Lean_Meta_instMonadMCtxMetaM;
x_93 = l_Lean_Expr_hasExprMVar(x_1);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasFVar(x_1);
if (x_94 == 0)
{
goto block_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
}
else
{
goto block_92;
}
block_92:
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_instantiateMVars___redArg(x_63, x_81, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = lean_apply_5(x_82, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Expr_hasExprMVar(x_84);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_hasFVar(x_84);
x_12 = x_85;
x_13 = x_84;
x_14 = x_87;
goto block_44;
}
else
{
x_12 = x_85;
x_13 = x_84;
x_14 = x_86;
goto block_44;
}
}
else
{
uint8_t x_88; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_122; 
x_97 = lean_ctor_get(x_65, 0);
x_98 = lean_ctor_get(x_65, 2);
x_99 = lean_ctor_get(x_65, 3);
x_100 = lean_ctor_get(x_65, 4);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
x_101 = l_Lean_Meta_whnfEasyCases___closed__4;
x_102 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_97);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_103, 0, x_97);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_104, 0, x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_106, 0, x_100);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_107, 0, x_99);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_108, 0, x_98);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set(x_109, 4, x_106);
lean_ctor_set(x_63, 1, x_102);
lean_ctor_set(x_63, 0, x_109);
x_110 = l_Lean_Meta_instMonadMCtxMetaM;
x_122 = l_Lean_Expr_hasExprMVar(x_1);
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = l_Lean_Expr_hasFVar(x_1);
if (x_123 == 0)
{
goto block_121;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_7);
return x_125;
}
}
else
{
goto block_121;
}
block_121:
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_instantiateMVars___redArg(x_63, x_110, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_112 = lean_apply_5(x_111, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_hasExprMVar(x_113);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Expr_hasFVar(x_113);
x_12 = x_114;
x_13 = x_113;
x_14 = x_116;
goto block_44;
}
else
{
x_12 = x_114;
x_13 = x_113;
x_14 = x_115;
goto block_44;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_154; 
x_126 = lean_ctor_get(x_63, 0);
lean_inc(x_126);
lean_dec(x_63);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
x_132 = l_Lean_Meta_whnfEasyCases___closed__4;
x_133 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_127);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_134, 0, x_127);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_135, 0, x_127);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_137, 0, x_130);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_138, 0, x_129);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_139, 0, x_128);
if (lean_is_scalar(x_131)) {
 x_140 = lean_alloc_ctor(0, 5, 0);
} else {
 x_140 = x_131;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_137);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_133);
x_142 = l_Lean_Meta_instMonadMCtxMetaM;
x_154 = l_Lean_Expr_hasExprMVar(x_1);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = l_Lean_Expr_hasFVar(x_1);
if (x_155 == 0)
{
goto block_153;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_7);
return x_157;
}
}
else
{
goto block_153;
}
block_153:
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Lean_instantiateMVars___redArg(x_141, x_142, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_144 = lean_apply_5(x_143, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Expr_hasExprMVar(x_145);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = l_Lean_Expr_hasFVar(x_145);
x_12 = x_146;
x_13 = x_145;
x_14 = x_148;
goto block_44;
}
else
{
x_12 = x_146;
x_13 = x_145;
x_14 = x_147;
goto block_44;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_151 = x_144;
} else {
 lean_dec_ref(x_144);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_201; 
x_158 = lean_ctor_get(x_47, 0);
x_159 = lean_ctor_get(x_47, 2);
x_160 = lean_ctor_get(x_47, 3);
x_161 = lean_ctor_get(x_47, 4);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_47);
x_162 = l_Lean_Meta_whnfEasyCases___closed__2;
x_163 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_158);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_164, 0, x_158);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_165, 0, x_158);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_167, 0, x_161);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_168, 0, x_160);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_169, 0, x_159);
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_162);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_168);
lean_ctor_set(x_170, 4, x_167);
lean_ctor_set(x_45, 1, x_163);
lean_ctor_set(x_45, 0, x_170);
x_171 = l_ReaderT_instMonad___redArg(x_45);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 3);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 4);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = l_Lean_Meta_whnfEasyCases___closed__4;
x_180 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_174);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_181, 0, x_174);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_182, 0, x_174);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_184, 0, x_177);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_185, 0, x_176);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_186, 0, x_175);
if (lean_is_scalar(x_178)) {
 x_187 = lean_alloc_ctor(0, 5, 0);
} else {
 x_187 = x_178;
}
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_186);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set(x_187, 4, x_184);
if (lean_is_scalar(x_173)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_173;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
x_189 = l_Lean_Meta_instMonadMCtxMetaM;
x_201 = l_Lean_Expr_hasExprMVar(x_1);
if (x_201 == 0)
{
uint8_t x_202; 
x_202 = l_Lean_Expr_hasFVar(x_1);
if (x_202 == 0)
{
goto block_200;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_188);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_7);
return x_204;
}
}
else
{
goto block_200;
}
block_200:
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Lean_instantiateMVars___redArg(x_188, x_189, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = lean_apply_5(x_190, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Expr_hasExprMVar(x_192);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Expr_hasFVar(x_192);
x_12 = x_193;
x_13 = x_192;
x_14 = x_195;
goto block_44;
}
else
{
x_12 = x_193;
x_13 = x_192;
x_14 = x_194;
goto block_44;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_ctor_get(x_191, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_198 = x_191;
} else {
 lean_dec_ref(x_191);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_251; 
x_205 = lean_ctor_get(x_45, 0);
lean_inc(x_205);
lean_dec(x_45);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 4);
lean_inc(x_209);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 lean_ctor_release(x_205, 4);
 x_210 = x_205;
} else {
 lean_dec_ref(x_205);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Meta_whnfEasyCases___closed__2;
x_212 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_206);
x_213 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_213, 0, x_206);
x_214 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_214, 0, x_206);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_216, 0, x_209);
x_217 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_217, 0, x_208);
x_218 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_218, 0, x_207);
if (lean_is_scalar(x_210)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_210;
}
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_211);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_217);
lean_ctor_set(x_219, 4, x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
x_221 = l_ReaderT_instMonad___redArg(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 4);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
x_229 = l_Lean_Meta_whnfEasyCases___closed__4;
x_230 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_224);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_231, 0, x_224);
x_232 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_232, 0, x_224);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_234, 0, x_227);
x_235 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_235, 0, x_226);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_236, 0, x_225);
if (lean_is_scalar(x_228)) {
 x_237 = lean_alloc_ctor(0, 5, 0);
} else {
 x_237 = x_228;
}
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_229);
lean_ctor_set(x_237, 2, x_236);
lean_ctor_set(x_237, 3, x_235);
lean_ctor_set(x_237, 4, x_234);
if (lean_is_scalar(x_223)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_223;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_230);
x_239 = l_Lean_Meta_instMonadMCtxMetaM;
x_251 = l_Lean_Expr_hasExprMVar(x_1);
if (x_251 == 0)
{
uint8_t x_252; 
x_252 = l_Lean_Expr_hasFVar(x_1);
if (x_252 == 0)
{
goto block_250;
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_238);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_7);
return x_254;
}
}
else
{
goto block_250;
}
block_250:
{
lean_object* x_240; lean_object* x_241; 
x_240 = l_Lean_instantiateMVars___redArg(x_238, x_239, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_241 = lean_apply_5(x_240, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Expr_hasExprMVar(x_242);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = l_Lean_Expr_hasFVar(x_242);
x_12 = x_243;
x_13 = x_242;
x_14 = x_245;
goto block_44;
}
else
{
x_12 = x_243;
x_13 = x_242;
x_14 = x_244;
goto block_44;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_241, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_248 = x_241;
} else {
 lean_dec_ref(x_241);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_44:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_whnf(x_13, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 4:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_24 = lean_string_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = x_20;
goto block_11;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_26 = lean_string_dec_eq(x_21, x_25);
lean_dec(x_21);
if (x_26 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = x_20;
goto block_11;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_apply_6(x_2, x_27, x_3, x_4, x_5, x_6, x_20);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_8 = x_29;
goto block_11;
}
}
else
{
lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_8 = x_30;
goto block_11;
}
}
else
{
lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_8 = x_31;
goto block_11;
}
}
case 9:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_apply_6(x_2, x_34, x_3, x_4, x_5, x_6, x_33);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_8 = x_36;
goto block_11;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_8 = x_37;
goto block_11;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_whnfEasyCases___closed__1;
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 2);
x_53 = lean_ctor_get(x_48, 3);
x_54 = lean_ctor_get(x_48, 4);
x_55 = lean_ctor_get(x_48, 1);
lean_dec(x_55);
x_56 = l_Lean_Meta_whnfEasyCases___closed__2;
x_57 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_53);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_52);
lean_ctor_set(x_48, 4, x_61);
lean_ctor_set(x_48, 3, x_62);
lean_ctor_set(x_48, 2, x_63);
lean_ctor_set(x_48, 1, x_56);
lean_ctor_set(x_48, 0, x_60);
lean_ctor_set(x_46, 1, x_57);
x_64 = l_ReaderT_instMonad___redArg(x_46);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_94; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 2);
x_71 = lean_ctor_get(x_66, 3);
x_72 = lean_ctor_get(x_66, 4);
x_73 = lean_ctor_get(x_66, 1);
lean_dec(x_73);
x_74 = l_Lean_Meta_whnfEasyCases___closed__4;
x_75 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
lean_ctor_set(x_66, 4, x_79);
lean_ctor_set(x_66, 3, x_80);
lean_ctor_set(x_66, 2, x_81);
lean_ctor_set(x_66, 1, x_74);
lean_ctor_set(x_66, 0, x_78);
lean_ctor_set(x_64, 1, x_75);
x_82 = l_Lean_Meta_instMonadMCtxMetaM;
x_94 = l_Lean_Expr_hasExprMVar(x_2);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasFVar(x_2);
if (x_95 == 0)
{
goto block_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_8);
return x_97;
}
}
else
{
goto block_93;
}
block_93:
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_instantiateMVars___redArg(x_64, x_82, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = lean_apply_5(x_83, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Expr_hasExprMVar(x_85);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_hasFVar(x_85);
x_13 = x_86;
x_14 = x_85;
x_15 = x_88;
goto block_45;
}
else
{
x_13 = x_86;
x_14 = x_85;
x_15 = x_87;
goto block_45;
}
}
else
{
uint8_t x_89; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_123; 
x_98 = lean_ctor_get(x_66, 0);
x_99 = lean_ctor_get(x_66, 2);
x_100 = lean_ctor_get(x_66, 3);
x_101 = lean_ctor_get(x_66, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_66);
x_102 = l_Lean_Meta_whnfEasyCases___closed__4;
x_103 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_98);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_104, 0, x_98);
x_105 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_105, 0, x_98);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_107, 0, x_101);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_108, 0, x_100);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_109, 0, x_99);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_102);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_107);
lean_ctor_set(x_64, 1, x_103);
lean_ctor_set(x_64, 0, x_110);
x_111 = l_Lean_Meta_instMonadMCtxMetaM;
x_123 = l_Lean_Expr_hasExprMVar(x_2);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_2);
if (x_124 == 0)
{
goto block_122;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_8);
return x_126;
}
}
else
{
goto block_122;
}
block_122:
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lean_instantiateMVars___redArg(x_64, x_111, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_113 = lean_apply_5(x_112, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Expr_hasExprMVar(x_114);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Expr_hasFVar(x_114);
x_13 = x_115;
x_14 = x_114;
x_15 = x_117;
goto block_45;
}
else
{
x_13 = x_115;
x_14 = x_114;
x_15 = x_116;
goto block_45;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_155; 
x_127 = lean_ctor_get(x_64, 0);
lean_inc(x_127);
lean_dec(x_64);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 4);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Meta_whnfEasyCases___closed__4;
x_134 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_128);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_135, 0, x_128);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_128);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_139, 0, x_130);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_140, 0, x_129);
if (lean_is_scalar(x_132)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_132;
}
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_139);
lean_ctor_set(x_141, 4, x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
x_143 = l_Lean_Meta_instMonadMCtxMetaM;
x_155 = l_Lean_Expr_hasExprMVar(x_2);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasFVar(x_2);
if (x_156 == 0)
{
goto block_154;
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_142);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_8);
return x_158;
}
}
else
{
goto block_154;
}
block_154:
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lean_instantiateMVars___redArg(x_142, x_143, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_145 = lean_apply_5(x_144, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Expr_hasExprMVar(x_146);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasFVar(x_146);
x_13 = x_147;
x_14 = x_146;
x_15 = x_149;
goto block_45;
}
else
{
x_13 = x_147;
x_14 = x_146;
x_15 = x_148;
goto block_45;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_202; 
x_159 = lean_ctor_get(x_48, 0);
x_160 = lean_ctor_get(x_48, 2);
x_161 = lean_ctor_get(x_48, 3);
x_162 = lean_ctor_get(x_48, 4);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_48);
x_163 = l_Lean_Meta_whnfEasyCases___closed__2;
x_164 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_159);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_165, 0, x_159);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_159);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_168, 0, x_162);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_169, 0, x_161);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_170, 0, x_160);
x_171 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_170);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set(x_171, 4, x_168);
lean_ctor_set(x_46, 1, x_164);
lean_ctor_set(x_46, 0, x_171);
x_172 = l_ReaderT_instMonad___redArg(x_46);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 4);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 lean_ctor_release(x_173, 4);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
x_180 = l_Lean_Meta_whnfEasyCases___closed__4;
x_181 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_175);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_182, 0, x_175);
x_183 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_183, 0, x_175);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_185, 0, x_178);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_186, 0, x_177);
x_187 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_187, 0, x_176);
if (lean_is_scalar(x_179)) {
 x_188 = lean_alloc_ctor(0, 5, 0);
} else {
 x_188 = x_179;
}
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_187);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set(x_188, 4, x_185);
if (lean_is_scalar(x_174)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_174;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_181);
x_190 = l_Lean_Meta_instMonadMCtxMetaM;
x_202 = l_Lean_Expr_hasExprMVar(x_2);
if (x_202 == 0)
{
uint8_t x_203; 
x_203 = l_Lean_Expr_hasFVar(x_2);
if (x_203 == 0)
{
goto block_201;
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_189);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_8);
return x_205;
}
}
else
{
goto block_201;
}
block_201:
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Lean_instantiateMVars___redArg(x_189, x_190, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_192 = lean_apply_5(x_191, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_Expr_hasExprMVar(x_193);
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = l_Lean_Expr_hasFVar(x_193);
x_13 = x_194;
x_14 = x_193;
x_15 = x_196;
goto block_45;
}
else
{
x_13 = x_194;
x_14 = x_193;
x_15 = x_195;
goto block_45;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_252; 
x_206 = lean_ctor_get(x_46, 0);
lean_inc(x_206);
lean_dec(x_46);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 4);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = l_Lean_Meta_whnfEasyCases___closed__2;
x_213 = l_Lean_Meta_whnfEasyCases___closed__3;
lean_inc(x_207);
x_214 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_214, 0, x_207);
x_215 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_215, 0, x_207);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_217, 0, x_210);
x_218 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_218, 0, x_209);
x_219 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_219, 0, x_208);
if (lean_is_scalar(x_211)) {
 x_220 = lean_alloc_ctor(0, 5, 0);
} else {
 x_220 = x_211;
}
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_212);
lean_ctor_set(x_220, 2, x_219);
lean_ctor_set(x_220, 3, x_218);
lean_ctor_set(x_220, 4, x_217);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_213);
x_222 = l_ReaderT_instMonad___redArg(x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_223, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 4);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 lean_ctor_release(x_223, 4);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
x_230 = l_Lean_Meta_whnfEasyCases___closed__4;
x_231 = l_Lean_Meta_whnfEasyCases___closed__5;
lean_inc(x_225);
x_232 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_232, 0, x_225);
x_233 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_233, 0, x_225);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_235, 0, x_228);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_236, 0, x_227);
x_237 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_237, 0, x_226);
if (lean_is_scalar(x_229)) {
 x_238 = lean_alloc_ctor(0, 5, 0);
} else {
 x_238 = x_229;
}
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_230);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set(x_238, 4, x_235);
if (lean_is_scalar(x_224)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_224;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_231);
x_240 = l_Lean_Meta_instMonadMCtxMetaM;
x_252 = l_Lean_Expr_hasExprMVar(x_2);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = l_Lean_Expr_hasFVar(x_2);
if (x_253 == 0)
{
goto block_251;
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_8);
return x_255;
}
}
else
{
goto block_251;
}
block_251:
{
lean_object* x_241; lean_object* x_242; 
x_241 = l_Lean_instantiateMVars___redArg(x_239, x_240, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_242 = lean_apply_5(x_241, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l_Lean_Expr_hasExprMVar(x_243);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = l_Lean_Expr_hasFVar(x_243);
x_13 = x_244;
x_14 = x_243;
x_15 = x_246;
goto block_45;
}
else
{
x_13 = x_244;
x_14 = x_243;
x_15 = x_245;
goto block_45;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_247 = lean_ctor_get(x_242, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_45:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_whnf(x_14, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 4:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = x_21;
goto block_12;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_27 = lean_string_dec_eq(x_22, x_26);
lean_dec(x_22);
if (x_27 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = x_21;
goto block_12;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_apply_6(x_3, x_28, x_4, x_5, x_6, x_7, x_21);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_9 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_9 = x_31;
goto block_12;
}
}
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_9 = x_32;
goto block_12;
}
}
case 9:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_apply_6(x_3, x_35, x_4, x_5, x_6, x_7, x_34);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_9 = x_37;
goto block_12;
}
}
default: 
{
lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_9 = x_38;
goto block_12;
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
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_56; 
x_56 = l_Lean_Expr_hasExprMVar(x_2);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasFVar(x_2);
if (x_57 == 0)
{
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
else
{
goto block_55;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_apply_1(x_1, x_12);
x_15 = l_Lean_mkRawNatLit(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
block_49:
{
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_whnf(x_20, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 4:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_31 = lean_string_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_dec(x_28);
lean_dec(x_1);
x_8 = x_27;
goto block_11;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_33 = lean_string_dec_eq(x_28, x_32);
lean_dec(x_28);
if (x_33 == 0)
{
lean_dec(x_1);
x_8 = x_27;
goto block_11;
}
else
{
lean_object* x_34; 
x_34 = lean_unsigned_to_nat(0u);
x_12 = x_34;
x_13 = x_27;
goto block_18;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_8 = x_35;
goto block_11;
}
}
else
{
lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_8 = x_36;
goto block_11;
}
}
else
{
lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_1);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_8 = x_37;
goto block_11;
}
}
case 9:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_12 = x_40;
x_13 = x_39;
goto block_18;
}
else
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_1);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_8 = x_41;
goto block_11;
}
}
default: 
{
lean_object* x_42; 
lean_dec(x_23);
lean_dec(x_1);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_dec(x_22);
x_8 = x_42;
goto block_11;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
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
lean_object* x_47; lean_object* x_48; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_19);
return x_48;
}
}
block_55:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_2, x_4, x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Expr_hasExprMVar(x_51);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_hasFVar(x_51);
x_19 = x_52;
x_20 = x_51;
x_21 = x_54;
goto block_49;
}
else
{
x_19 = x_52;
x_20 = x_51;
x_21 = x_53;
goto block_49;
}
}
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isDefEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBinOp", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__1;
x_2 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4;
x_3 = l_Lean_Meta_reduceBinNatOp___closed__0;
x_4 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" op ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_165; 
x_165 = l_Lean_Expr_hasExprMVar(x_2);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = l_Lean_Expr_hasFVar(x_2);
if (x_166 == 0)
{
goto block_164;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_8);
return x_168;
}
}
else
{
goto block_164;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_apply_2(x_1, x_17, x_18);
x_21 = l_Lean_mkRawNatLit(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
block_68:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_32, x_29, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_17 = x_25;
x_18 = x_26;
x_19 = x_36;
goto block_24;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_unfoldDefinition___closed__2;
lean_inc(x_25);
x_41 = l_Nat_reprFast(x_25);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_MessageData_ofFormat(x_42);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_43);
lean_ctor_set(x_33, 0, x_40);
x_44 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_26);
x_46 = l_Nat_reprFast(x_26);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
x_51 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_32, x_50, x_27, x_28, x_29, x_30, x_38);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_17 = x_25;
x_18 = x_26;
x_19 = x_52;
goto block_24;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_dec(x_33);
x_54 = l_Lean_Meta_unfoldDefinition___closed__2;
lean_inc(x_25);
x_55 = l_Nat_reprFast(x_25);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_MessageData_ofFormat(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_26);
x_61 = l_Nat_reprFast(x_26);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_MessageData_ofFormat(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_54);
x_66 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_32, x_65, x_27, x_28, x_29, x_30, x_53);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_17 = x_25;
x_18 = x_26;
x_19 = x_67;
goto block_24;
}
}
}
block_104:
{
if (x_76 == 0)
{
lean_object* x_77; 
lean_inc(x_75);
lean_inc(x_69);
lean_inc(x_71);
lean_inc(x_70);
x_77 = lean_whnf(x_74, x_70, x_71, x_69, x_75, x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
switch (lean_obj_tag(x_78)) {
case 4:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_86 = lean_string_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_dec(x_83);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_9 = x_82;
goto block_12;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_88 = lean_string_dec_eq(x_83, x_87);
lean_dec(x_83);
if (x_88 == 0)
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_9 = x_82;
goto block_12;
}
else
{
lean_object* x_89; 
x_89 = lean_unsigned_to_nat(0u);
x_25 = x_73;
x_26 = x_89;
x_27 = x_70;
x_28 = x_71;
x_29 = x_69;
x_30 = x_75;
x_31 = x_82;
goto block_68;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
lean_dec(x_77);
x_9 = x_90;
goto block_12;
}
}
else
{
lean_object* x_91; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_dec(x_77);
x_9 = x_91;
goto block_12;
}
}
else
{
lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_92 = lean_ctor_get(x_77, 1);
lean_inc(x_92);
lean_dec(x_77);
x_9 = x_92;
goto block_12;
}
}
case 9:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_78, 0);
lean_inc(x_93);
lean_dec(x_78);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_dec(x_77);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_25 = x_73;
x_26 = x_95;
x_27 = x_70;
x_28 = x_71;
x_29 = x_69;
x_30 = x_75;
x_31 = x_94;
goto block_68;
}
else
{
lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_dec(x_77);
x_9 = x_96;
goto block_12;
}
}
default: 
{
lean_object* x_97; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_97 = lean_ctor_get(x_77, 1);
lean_inc(x_97);
lean_dec(x_77);
x_9 = x_97;
goto block_12;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_77);
if (x_98 == 0)
{
return x_77;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_77, 0);
x_100 = lean_ctor_get(x_77, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_77);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_72);
return x_103;
}
}
block_116:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_3, x_107, x_109);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Expr_hasExprMVar(x_112);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = l_Lean_Expr_hasFVar(x_112);
x_69 = x_105;
x_70 = x_106;
x_71 = x_107;
x_72 = x_113;
x_73 = x_108;
x_74 = x_112;
x_75 = x_110;
x_76 = x_115;
goto block_104;
}
else
{
x_69 = x_105;
x_70 = x_106;
x_71 = x_107;
x_72 = x_113;
x_73 = x_108;
x_74 = x_112;
x_75 = x_110;
x_76 = x_114;
goto block_104;
}
}
block_127:
{
uint8_t x_123; 
x_123 = l_Lean_Expr_hasExprMVar(x_3);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_3);
if (x_124 == 0)
{
x_105 = x_120;
x_106 = x_118;
x_107 = x_119;
x_108 = x_117;
x_109 = x_122;
x_110 = x_121;
goto block_116;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_1);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
else
{
x_105 = x_120;
x_106 = x_118;
x_107 = x_119;
x_108 = x_117;
x_109 = x_122;
x_110 = x_121;
goto block_116;
}
}
block_158:
{
if (x_130 == 0)
{
lean_object* x_131; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_131 = lean_whnf(x_129, x_4, x_5, x_6, x_7, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
switch (lean_obj_tag(x_132)) {
case 4:
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_140 = lean_string_dec_eq(x_138, x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_dec(x_137);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_136;
goto block_16;
}
else
{
lean_object* x_141; uint8_t x_142; 
x_141 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_142 = lean_string_dec_eq(x_137, x_141);
lean_dec(x_137);
if (x_142 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_136;
goto block_16;
}
else
{
lean_object* x_143; 
x_143 = lean_unsigned_to_nat(0u);
x_117 = x_143;
x_118 = x_4;
x_119 = x_5;
x_120 = x_6;
x_121 = x_7;
x_122 = x_136;
goto block_127;
}
}
}
else
{
lean_object* x_144; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_ctor_get(x_131, 1);
lean_inc(x_144);
lean_dec(x_131);
x_13 = x_144;
goto block_16;
}
}
else
{
lean_object* x_145; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_145 = lean_ctor_get(x_131, 1);
lean_inc(x_145);
lean_dec(x_131);
x_13 = x_145;
goto block_16;
}
}
else
{
lean_object* x_146; 
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_131, 1);
lean_inc(x_146);
lean_dec(x_131);
x_13 = x_146;
goto block_16;
}
}
case 9:
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
lean_dec(x_132);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_131, 1);
lean_inc(x_148);
lean_dec(x_131);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_117 = x_149;
x_118 = x_4;
x_119 = x_5;
x_120 = x_6;
x_121 = x_7;
x_122 = x_148;
goto block_127;
}
else
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_ctor_get(x_131, 1);
lean_inc(x_150);
lean_dec(x_131);
x_13 = x_150;
goto block_16;
}
}
default: 
{
lean_object* x_151; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
lean_dec(x_131);
x_13 = x_151;
goto block_16;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_129);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_128);
return x_157;
}
}
block_164:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_2, x_5, x_8);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_Expr_hasExprMVar(x_160);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Expr_hasFVar(x_160);
x_128 = x_161;
x_129 = x_160;
x_130 = x_163;
goto block_158;
}
else
{
x_128 = x_161;
x_129 = x_160;
x_130 = x_162;
goto block_158;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg(x_1, x_4, x_6);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0;
x_23 = lean_box(0);
x_24 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_26);
x_27 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_8);
x_29 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_29);
x_30 = lean_st_ref_set(x_6, x_13, x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint64_t x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec(x_14);
x_39 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0;
x_40 = lean_box(0);
x_41 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_39);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_43);
x_44 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1;
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_45);
lean_ctor_set(x_12, 0, x_8);
x_46 = l_Lean_PersistentArray_push___redArg(x_38, x_12);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_37);
lean_ctor_set(x_13, 4, x_47);
x_48 = lean_st_ref_set(x_6, x_13, x_16);
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
x_51 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
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
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; double x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
x_55 = lean_ctor_get(x_13, 2);
x_56 = lean_ctor_get(x_13, 3);
x_57 = lean_ctor_get(x_13, 5);
x_58 = lean_ctor_get(x_13, 6);
x_59 = lean_ctor_get(x_13, 7);
x_60 = lean_ctor_get(x_13, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_61 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_63 = x_14;
} else {
 lean_dec_ref(x_14);
 x_63 = lean_box(0);
}
x_64 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0;
x_65 = lean_box(0);
x_66 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_67 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_float(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_float(x_67, sizeof(void*)*2 + 8, x_64);
x_68 = lean_unbox(x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 16, x_68);
x_69 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1;
x_70 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_10);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_70);
lean_ctor_set(x_12, 0, x_8);
x_71 = l_Lean_PersistentArray_push___redArg(x_62, x_12);
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_61);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_55);
lean_ctor_set(x_73, 3, x_56);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_57);
lean_ctor_set(x_73, 6, x_58);
lean_ctor_set(x_73, 7, x_59);
lean_ctor_set(x_73, 8, x_60);
x_74 = lean_st_ref_set(x_6, x_73, x_16);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_dec(x_12);
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_13, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_13, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_13, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_13, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_13, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_13, 8);
lean_inc(x_87);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_88 = x_13;
} else {
 lean_dec_ref(x_13);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_90 = lean_ctor_get(x_14, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_91 = x_14;
} else {
 lean_dec_ref(x_14);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0;
x_93 = lean_box(0);
x_94 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
x_96 = lean_unbox(x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_96);
x_97 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1;
x_98 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 2, x_97);
lean_inc(x_8);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_8);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_PersistentArray_push___redArg(x_90, x_99);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 1, 8);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint64(x_101, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_102 = lean_alloc_ctor(0, 9, 0);
} else {
 x_102 = x_88;
}
lean_ctor_set(x_102, 0, x_80);
lean_ctor_set(x_102, 1, x_81);
lean_ctor_set(x_102, 2, x_82);
lean_ctor_set(x_102, 3, x_83);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_84);
lean_ctor_set(x_102, 6, x_85);
lean_ctor_set(x_102, 7, x_86);
lean_ctor_set(x_102, 8, x_87);
x_103 = lean_st_ref_set(x_6, x_102, x_79);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2;
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
static lean_object* _init_l_Lean_Meta_reducePow___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ^ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reducePow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reducePow___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reducePow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_193; 
x_193 = l_Lean_Expr_hasExprMVar(x_1);
if (x_193 == 0)
{
uint8_t x_194; 
x_194 = l_Lean_Expr_hasFVar(x_1);
if (x_194 == 0)
{
goto block_192;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_7);
return x_196;
}
}
else
{
goto block_192;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_nat_pow(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
x_20 = l_Lean_mkRawNatLit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_96:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_28);
lean_inc(x_25);
x_31 = l_Lean_checkExponent(x_25, x_28, x_29, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_42 = l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg(x_41, x_28, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_free_object(x_43);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_16 = x_25;
x_17 = x_24;
x_18 = x_47;
goto block_23;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_42, 1);
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_unfoldDefinition___closed__2;
lean_inc(x_24);
x_52 = l_Nat_reprFast(x_24);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 0, x_52);
x_53 = l_Lean_MessageData_ofFormat(x_43);
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_51);
x_54 = l_Lean_Meta_reducePow___closed__1;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_25);
x_56 = l_Nat_reprFast(x_25);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
x_61 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(x_41, x_60, x_26, x_27, x_28, x_29, x_49);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_16 = x_25;
x_17 = x_24;
x_18 = x_62;
goto block_23;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_dec(x_42);
x_64 = l_Lean_Meta_unfoldDefinition___closed__2;
lean_inc(x_24);
x_65 = l_Nat_reprFast(x_24);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 0, x_65);
x_66 = l_Lean_MessageData_ofFormat(x_43);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_reducePow___closed__1;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_25);
x_70 = l_Nat_reprFast(x_25);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_MessageData_ofFormat(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
x_75 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(x_41, x_74, x_26, x_27, x_28, x_29, x_63);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_16 = x_25;
x_17 = x_24;
x_18 = x_76;
goto block_23;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_43, 0);
lean_inc(x_77);
lean_dec(x_43);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_79 = lean_ctor_get(x_42, 1);
lean_inc(x_79);
lean_dec(x_42);
x_16 = x_25;
x_17 = x_24;
x_18 = x_79;
goto block_23;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_80 = lean_ctor_get(x_42, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_81 = x_42;
} else {
 lean_dec_ref(x_42);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_unfoldDefinition___closed__2;
lean_inc(x_24);
x_83 = l_Nat_reprFast(x_24);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_MessageData_ofFormat(x_84);
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(7, 2, 0);
} else {
 x_86 = x_81;
 lean_ctor_set_tag(x_86, 7);
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Meta_reducePow___closed__1;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_25);
x_89 = l_Nat_reprFast(x_25);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_MessageData_ofFormat(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
x_94 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(x_41, x_93, x_26, x_27, x_28, x_29, x_80);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_16 = x_25;
x_17 = x_24;
x_18 = x_95;
goto block_23;
}
}
}
}
block_132:
{
if (x_104 == 0)
{
lean_object* x_105; 
lean_inc(x_100);
lean_inc(x_101);
lean_inc(x_98);
lean_inc(x_102);
x_105 = lean_whnf(x_97, x_102, x_98, x_101, x_100, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
switch (lean_obj_tag(x_106)) {
case 4:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_114 = lean_string_dec_eq(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_dec(x_111);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_8 = x_110;
goto block_11;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_116 = lean_string_dec_eq(x_111, x_115);
lean_dec(x_111);
if (x_116 == 0)
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_8 = x_110;
goto block_11;
}
else
{
lean_object* x_117; 
x_117 = lean_unsigned_to_nat(0u);
x_24 = x_99;
x_25 = x_117;
x_26 = x_102;
x_27 = x_98;
x_28 = x_101;
x_29 = x_100;
x_30 = x_110;
goto block_96;
}
}
}
else
{
lean_object* x_118; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
lean_dec(x_105);
x_8 = x_118;
goto block_11;
}
}
else
{
lean_object* x_119; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_119 = lean_ctor_get(x_105, 1);
lean_inc(x_119);
lean_dec(x_105);
x_8 = x_119;
goto block_11;
}
}
else
{
lean_object* x_120; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_120 = lean_ctor_get(x_105, 1);
lean_inc(x_120);
lean_dec(x_105);
x_8 = x_120;
goto block_11;
}
}
case 9:
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_106, 0);
lean_inc(x_121);
lean_dec(x_106);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_105, 1);
lean_inc(x_122);
lean_dec(x_105);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_24 = x_99;
x_25 = x_123;
x_26 = x_102;
x_27 = x_98;
x_28 = x_101;
x_29 = x_100;
x_30 = x_122;
goto block_96;
}
else
{
lean_object* x_124; 
lean_dec(x_121);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_dec(x_105);
x_8 = x_124;
goto block_11;
}
}
default: 
{
lean_object* x_125; 
lean_dec(x_106);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_125 = lean_ctor_get(x_105, 1);
lean_inc(x_125);
lean_dec(x_105);
x_8 = x_125;
goto block_11;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_126 = !lean_is_exclusive(x_105);
if (x_126 == 0)
{
return x_105;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_105, 0);
x_128 = lean_ctor_get(x_105, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_105);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_103);
return x_131;
}
}
block_144:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_2, x_133, x_135);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Expr_hasExprMVar(x_140);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Expr_hasFVar(x_140);
x_97 = x_140;
x_98 = x_133;
x_99 = x_134;
x_100 = x_136;
x_101 = x_137;
x_102 = x_138;
x_103 = x_141;
x_104 = x_143;
goto block_132;
}
else
{
x_97 = x_140;
x_98 = x_133;
x_99 = x_134;
x_100 = x_136;
x_101 = x_137;
x_102 = x_138;
x_103 = x_141;
x_104 = x_142;
goto block_132;
}
}
block_155:
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasExprMVar(x_2);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = l_Lean_Expr_hasFVar(x_2);
if (x_152 == 0)
{
x_133 = x_147;
x_134 = x_145;
x_135 = x_150;
x_136 = x_149;
x_137 = x_148;
x_138 = x_146;
goto block_144;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_2);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
}
else
{
x_133 = x_147;
x_134 = x_145;
x_135 = x_150;
x_136 = x_149;
x_137 = x_148;
x_138 = x_146;
goto block_144;
}
}
block_186:
{
if (x_158 == 0)
{
lean_object* x_159; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_159 = lean_whnf(x_156, x_3, x_4, x_5, x_6, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
switch (lean_obj_tag(x_160)) {
case 4:
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 1)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_168 = lean_string_dec_eq(x_166, x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_dec(x_165);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_164;
goto block_15;
}
else
{
lean_object* x_169; uint8_t x_170; 
x_169 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_170 = lean_string_dec_eq(x_165, x_169);
lean_dec(x_165);
if (x_170 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_164;
goto block_15;
}
else
{
lean_object* x_171; 
x_171 = lean_unsigned_to_nat(0u);
x_145 = x_171;
x_146 = x_3;
x_147 = x_4;
x_148 = x_5;
x_149 = x_6;
x_150 = x_164;
goto block_155;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_ctor_get(x_159, 1);
lean_inc(x_172);
lean_dec(x_159);
x_12 = x_172;
goto block_15;
}
}
else
{
lean_object* x_173; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = lean_ctor_get(x_159, 1);
lean_inc(x_173);
lean_dec(x_159);
x_12 = x_173;
goto block_15;
}
}
else
{
lean_object* x_174; 
lean_dec(x_161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
lean_dec(x_159);
x_12 = x_174;
goto block_15;
}
}
case 9:
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
lean_dec(x_160);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_159, 1);
lean_inc(x_176);
lean_dec(x_159);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec(x_175);
x_145 = x_177;
x_146 = x_3;
x_147 = x_4;
x_148 = x_5;
x_149 = x_6;
x_150 = x_176;
goto block_155;
}
else
{
lean_object* x_178; 
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_159, 1);
lean_inc(x_178);
lean_dec(x_159);
x_12 = x_178;
goto block_15;
}
}
default: 
{
lean_object* x_179; 
lean_dec(x_160);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_ctor_get(x_159, 1);
lean_inc(x_179);
lean_dec(x_159);
x_12 = x_179;
goto block_15;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_159);
if (x_180 == 0)
{
return x_159;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_159, 0);
x_182 = lean_ctor_get(x_159, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_159);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_157);
return x_185;
}
}
block_192:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_7);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_Expr_hasExprMVar(x_188);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = l_Lean_Expr_hasFVar(x_188);
x_156 = x_188;
x_157 = x_189;
x_158 = x_191;
goto block_186;
}
else
{
x_156 = x_188;
x_157 = x_189;
x_158 = x_190;
goto block_186;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_reducePow_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_126; 
x_126 = l_Lean_Expr_hasExprMVar(x_2);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = l_Lean_Expr_hasFVar(x_2);
if (x_127 == 0)
{
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_8);
return x_129;
}
}
else
{
goto block_125;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
block_29:
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_apply_2(x_1, x_22, x_23);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Meta_reduceNative_x3f___closed__6;
x_17 = x_24;
x_18 = x_27;
goto block_21;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Meta_reduceNative_x3f___closed__9;
x_17 = x_24;
x_18 = x_28;
goto block_21;
}
}
block_65:
{
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_whnf(x_30, x_31, x_33, x_34, x_35, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
switch (lean_obj_tag(x_39)) {
case 4:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_1);
x_13 = x_43;
goto block_16;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_49 = lean_string_dec_eq(x_44, x_48);
lean_dec(x_44);
if (x_49 == 0)
{
lean_dec(x_36);
lean_dec(x_1);
x_13 = x_43;
goto block_16;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_22 = x_36;
x_23 = x_50;
x_24 = x_43;
goto block_29;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
x_13 = x_51;
goto block_16;
}
}
else
{
lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_1);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_dec(x_38);
x_13 = x_52;
goto block_16;
}
}
else
{
lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_1);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_dec(x_38);
x_13 = x_53;
goto block_16;
}
}
case 9:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec(x_39);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_dec(x_38);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_22 = x_36;
x_23 = x_56;
x_24 = x_55;
goto block_29;
}
else
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_1);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_dec(x_38);
x_13 = x_57;
goto block_16;
}
}
default: 
{
lean_object* x_58; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_1);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_dec(x_38);
x_13 = x_58;
goto block_16;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_36);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_32);
return x_64;
}
}
block_77:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_3, x_68, x_67);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Expr_hasExprMVar(x_73);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Expr_hasFVar(x_73);
x_30 = x_73;
x_31 = x_66;
x_32 = x_74;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_76;
goto block_65;
}
else
{
x_30 = x_73;
x_31 = x_66;
x_32 = x_74;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_75;
goto block_65;
}
}
block_88:
{
uint8_t x_84; 
x_84 = l_Lean_Expr_hasExprMVar(x_3);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = l_Lean_Expr_hasFVar(x_3);
if (x_85 == 0)
{
x_66 = x_79;
x_67 = x_83;
x_68 = x_80;
x_69 = x_81;
x_70 = x_82;
x_71 = x_78;
goto block_77;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
else
{
x_66 = x_79;
x_67 = x_83;
x_68 = x_80;
x_69 = x_81;
x_70 = x_82;
x_71 = x_78;
goto block_77;
}
}
block_119:
{
if (x_91 == 0)
{
lean_object* x_92; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_92 = lean_whnf(x_90, x_4, x_5, x_6, x_7, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
switch (lean_obj_tag(x_93)) {
case 4:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_101 = lean_string_dec_eq(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_dec(x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = x_97;
goto block_12;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Meta_withNatValue___redArg___closed__0;
x_103 = lean_string_dec_eq(x_98, x_102);
lean_dec(x_98);
if (x_103 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = x_97;
goto block_12;
}
else
{
lean_object* x_104; 
x_104 = lean_unsigned_to_nat(0u);
x_78 = x_104;
x_79 = x_4;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_97;
goto block_88;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
lean_dec(x_92);
x_9 = x_105;
goto block_12;
}
}
else
{
lean_object* x_106; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
lean_dec(x_92);
x_9 = x_106;
goto block_12;
}
}
else
{
lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_92, 1);
lean_inc(x_107);
lean_dec(x_92);
x_9 = x_107;
goto block_12;
}
}
case 9:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_93, 0);
lean_inc(x_108);
lean_dec(x_93);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_dec(x_92);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_78 = x_110;
x_79 = x_4;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_109;
goto block_88;
}
else
{
lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_ctor_get(x_92, 1);
lean_inc(x_111);
lean_dec(x_92);
x_9 = x_111;
goto block_12;
}
}
default: 
{
lean_object* x_112; 
lean_dec(x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_dec(x_92);
x_9 = x_112;
goto block_12;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_92);
if (x_113 == 0)
{
return x_92;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_92, 0);
x_115 = lean_ctor_get(x_92, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_92);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_89);
return x_118;
}
}
block_125:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_2, x_5, x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Expr_hasExprMVar(x_121);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_121);
x_89 = x_122;
x_90 = x_121;
x_91 = x_124;
goto block_119;
}
else
{
x_89 = x_122;
x_90 = x_121;
x_91 = x_123;
goto block_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNat_x3f___closed__0;
x_2 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("div", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pow", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gcd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ble", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("land", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lor", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("xor", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftLeft", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftRight", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_ble___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_gcd___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_reduceNat_x3f___closed__1;
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNat_x3f___lam__0___boxed), 1, 0);
x_23 = l_Lean_Meta_reduceUnaryNatOp(x_22, x_16, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
}
case 5:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_Meta_canUnfoldAtMatcher___closed__32;
x_33 = lean_string_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_reduceNat_x3f___closed__2;
x_35 = lean_string_dec_eq(x_30, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_reduceNat_x3f___closed__3;
x_37 = lean_string_dec_eq(x_30, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_reduceNat_x3f___closed__4;
x_39 = lean_string_dec_eq(x_30, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_reduceNat_x3f___closed__5;
x_41 = lean_string_dec_eq(x_30, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Meta_canUnfoldAtMatcher___closed__29;
x_43 = lean_string_dec_eq(x_30, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Meta_reduceNat_x3f___closed__6;
x_45 = lean_string_dec_eq(x_30, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_reduceNat_x3f___closed__7;
x_47 = lean_string_dec_eq(x_30, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_reduceNat_x3f___closed__8;
x_49 = lean_string_dec_eq(x_30, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Meta_reduceNat_x3f___closed__9;
x_51 = lean_string_dec_eq(x_30, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_53 = lean_string_dec_eq(x_30, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Meta_reduceNat_x3f___closed__11;
x_55 = lean_string_dec_eq(x_30, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_reduceNat_x3f___closed__12;
x_57 = lean_string_dec_eq(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Meta_reduceNat_x3f___closed__13;
x_59 = lean_string_dec_eq(x_30, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Meta_reduceNat_x3f___closed__14;
x_61 = lean_string_dec_eq(x_30, x_60);
lean_dec(x_30);
if (x_61 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Meta_reduceNat_x3f___closed__15;
x_63 = l_Lean_Meta_reduceBinNatOp(x_62, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_30);
x_64 = l_Lean_Meta_reduceNat_x3f___closed__16;
x_65 = l_Lean_Meta_reduceBinNatOp(x_64, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_30);
x_66 = l_Lean_Meta_reduceNat_x3f___closed__17;
x_67 = l_Lean_Meta_reduceBinNatOp(x_66, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_30);
x_68 = l_Lean_Meta_reduceNat_x3f___closed__18;
x_69 = l_Lean_Meta_reduceBinNatOp(x_68, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_30);
x_70 = l_Lean_Meta_reduceNat_x3f___closed__19;
x_71 = l_Lean_Meta_reduceBinNatOp(x_70, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_30);
x_72 = l_Lean_Meta_reduceNat_x3f___closed__20;
x_73 = l_Lean_Meta_reduceBinNatPred(x_72, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_30);
x_74 = l_Lean_Meta_reduceNat_x3f___closed__21;
x_75 = l_Lean_Meta_reduceBinNatPred(x_74, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_30);
x_76 = l_Lean_Meta_reduceNat_x3f___closed__22;
x_77 = l_Lean_Meta_reduceBinNatOp(x_76, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_30);
x_78 = l_Lean_Meta_reducePow(x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_30);
x_79 = l_Lean_Meta_reduceNat_x3f___closed__23;
x_80 = l_Lean_Meta_reduceBinNatOp(x_79, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_30);
x_81 = l_Lean_Meta_reduceNat_x3f___closed__24;
x_82 = l_Lean_Meta_reduceBinNatOp(x_81, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_30);
x_83 = l_Lean_Meta_reduceNat_x3f___closed__25;
x_84 = l_Lean_Meta_reduceBinNatOp(x_83, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_30);
x_85 = l_Lean_Meta_reduceNat_x3f___closed__26;
x_86 = l_Lean_Meta_reduceBinNatOp(x_85, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_30);
x_87 = l_Lean_Meta_reduceNat_x3f___closed__27;
x_88 = l_Lean_Meta_reduceBinNatOp(x_87, x_29, x_28, x_2, x_3, x_4, x_5, x_6);
return x_88;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_6;
goto block_14;
}
}
else
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_6;
goto block_14;
}
}
else
{
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_6;
goto block_14;
}
}
else
{
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_6;
goto block_10;
}
}
default: 
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_6;
goto block_10;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_6;
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_reduceNat_x3f___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_12; 
x_12 = l_Lean_Expr_hasFVar(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasExprMVar(x_1);
x_7 = x_13;
goto block_11;
}
else
{
x_7 = x_12;
goto block_11;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
goto block_6;
}
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_10; uint8_t x_15; 
x_15 = l_Lean_Expr_hasFVar(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_hasExprMVar(x_1);
x_10 = x_16;
goto block_14;
}
else
{
x_10 = x_15;
goto block_14;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
goto block_9;
}
}
else
{
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableExprConfigCacheKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_2, x_3, x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0;
x_17 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1;
x_18 = l_Lean_PersistentHashMap_find_x3f___redArg(x_16, x_17, x_15, x_14);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 3);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0;
x_23 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1;
x_24 = l_Lean_PersistentHashMap_find_x3f___redArg(x_22, x_23, x_21, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_2, x_3, x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_14, 3);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0;
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1;
x_20 = l_Lean_PersistentHashMap_find_x3f___redArg(x_18, x_19, x_17, x_16);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_ctor_get(x_14, 3);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0;
x_25 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1;
x_26 = l_Lean_PersistentHashMap_find_x3f___redArg(x_24, x_25, x_23, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_2, x_4, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_3);
x_19 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_18, x_9, x_3);
lean_ctor_set(x_13, 3, x_19);
x_20 = lean_st_ref_set(x_5, x_12, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_3);
x_31 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_28, x_9, x_3);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set(x_12, 1, x_32);
x_33 = lean_st_ref_set(x_5, x_12, x_14);
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
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 2);
x_39 = lean_ctor_get(x_12, 3);
x_40 = lean_ctor_get(x_12, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_47 = x_13;
} else {
 lean_dec_ref(x_13);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_44, x_9, x_3);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_46);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_38);
lean_ctor_set(x_50, 3, x_39);
lean_ctor_set(x_50, 4, x_40);
x_51 = lean_st_ref_set(x_5, x_50, x_14);
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
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Non-easy whnf: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1;
x_9 = l_Lean_MessageData_ofExpr(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_unfoldDefinition___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_checkSystem(x_1, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Lean_Meta_whnfCore_go(x_2, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l_Lean_Meta_reduceNat_x3f(x_12, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l_Lean_Meta_reduceNative_x3f(x_12, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_22 = l_Lean_Meta_unfoldDefinition_x3f(x_12, x_21, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_3, x_2, x_12, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_5);
lean_inc(x_4);
x_28 = lean_whnf(x_27, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_3, x_2, x_29, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_28;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_18, 0);
lean_inc(x_37);
lean_dec(x_18);
x_38 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_3, x_2, x_37, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_dec(x_14);
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___redArg(x_3, x_2, x_44, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Meta_whnfEasyCases___closed__10;
x_8 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_FVarId_getDecl___redArg(x_9, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 4);
lean_inc(x_17);
x_18 = l_Lean_Meta_getConfig___redArg(x_2, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_54; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_54 = l_Lean_LocalDecl_isImplementationDetail(x_11);
lean_dec(x_11);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_20, 16);
lean_dec(x_20);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_57, x_9);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_dec(x_58);
lean_free_object(x_18);
lean_dec(x_1);
x_22 = x_2;
x_23 = x_56;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
goto block_47;
}
}
else
{
lean_free_object(x_18);
lean_dec(x_1);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_53;
}
}
else
{
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_1);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_53;
}
block_47:
{
if (x_23 == 0)
{
lean_dec(x_9);
x_1 = x_17;
x_2 = x_22;
x_3 = x_24;
x_4 = x_25;
x_5 = x_26;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_24, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_29, 2);
x_33 = l_Lean_FVarIdSet_insert(x_32, x_9);
lean_ctor_set(x_29, 2, x_33);
x_34 = lean_st_ref_set(x_24, x_29, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_1 = x_17;
x_2 = x_22;
x_3 = x_24;
x_4 = x_25;
x_5 = x_26;
x_6 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_ctor_get(x_29, 3);
x_41 = lean_ctor_get(x_29, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_42 = l_Lean_FVarIdSet_insert(x_39, x_9);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_st_ref_set(x_24, x_43, x_30);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_1 = x_17;
x_2 = x_22;
x_3 = x_24;
x_4 = x_25;
x_5 = x_26;
x_6 = x_45;
goto _start;
}
}
}
block_53:
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_48, sizeof(void*)*7 + 8);
x_22 = x_48;
x_23 = x_52;
x_24 = x_49;
x_25 = x_50;
x_26 = x_51;
goto block_47;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_88; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_88 = l_Lean_LocalDecl_isImplementationDetail(x_11);
lean_dec(x_11);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_59, 16);
lean_dec(x_59);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
x_92 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_91, x_9);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_60);
return x_93;
}
else
{
lean_dec(x_92);
lean_dec(x_1);
x_61 = x_2;
x_62 = x_90;
x_63 = x_3;
x_64 = x_4;
x_65 = x_5;
goto block_81;
}
}
else
{
lean_dec(x_1);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
goto block_87;
}
}
else
{
lean_dec(x_59);
lean_dec(x_1);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
goto block_87;
}
block_81:
{
if (x_62 == 0)
{
lean_dec(x_9);
x_1 = x_17;
x_2 = x_61;
x_3 = x_63;
x_4 = x_64;
x_5 = x_65;
x_6 = x_60;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_st_ref_take(x_63, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 4);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
x_76 = l_Lean_FVarIdSet_insert(x_72, x_9);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_74);
x_78 = lean_st_ref_set(x_63, x_77, x_69);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_1 = x_17;
x_2 = x_61;
x_3 = x_63;
x_4 = x_64;
x_5 = x_65;
x_6 = x_79;
goto _start;
}
}
block_87:
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_82, sizeof(void*)*7 + 8);
x_61 = x_82;
x_62 = x_86;
x_63 = x_83;
x_64 = x_84;
x_65 = x_85;
goto block_81;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_10);
if (x_94 == 0)
{
return x_10;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 2:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(x_98, x_3, x_6);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_1);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
x_1 = x_106;
x_6 = x_105;
goto _start;
}
}
case 3:
{
lean_object* x_108; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_6);
return x_108;
}
case 6:
{
lean_object* x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_6);
return x_109;
}
case 7:
{
lean_object* x_110; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_6);
return x_110;
}
case 9:
{
lean_object* x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_6);
return x_111;
}
case 10:
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_1 = x_112;
goto _start;
}
default: 
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; uint8_t x_129; uint8_t x_152; 
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___boxed), 7, 1);
lean_closure_set(x_114, 0, x_1);
x_152 = l_Lean_Expr_hasFVar(x_1);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = l_Lean_Expr_hasExprMVar(x_1);
x_129 = x_153;
goto block_151;
}
else
{
x_129 = x_152;
goto block_151;
}
block_125:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_117 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4;
x_118 = lean_box(x_115);
x_119 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1___boxed), 8, 3);
lean_closure_set(x_119, 0, x_117);
lean_closure_set(x_119, 1, x_1);
lean_closure_set(x_119, 2, x_118);
x_120 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
x_121 = lean_box(1);
x_122 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_123 = lean_unbox(x_121);
x_124 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(x_120, x_114, x_119, x_123, x_122, x_2, x_3, x_4, x_5, x_116);
return x_124;
}
block_128:
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_box(0);
x_127 = lean_unbox(x_126);
x_115 = x_127;
x_116 = x_6;
goto block_125;
}
block_151:
{
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_2, 6);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_131 = lean_box(1);
x_132 = lean_st_ref_get(x_3, x_6);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_1);
x_135 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_134);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 1);
x_140 = lean_ctor_get(x_136, 3);
lean_inc(x_140);
lean_dec(x_136);
x_141 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_140, x_138);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
lean_free_object(x_135);
x_142 = lean_unbox(x_131);
x_115 = x_142;
x_116 = x_139;
goto block_125;
}
else
{
lean_object* x_143; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
lean_ctor_set(x_135, 0, x_143);
return x_135;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_135);
x_146 = lean_ctor_get(x_136, 3);
lean_inc(x_146);
lean_dec(x_136);
x_147 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_146, x_144);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = lean_unbox(x_131);
x_115 = x_148;
x_116 = x_145;
goto block_125;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
return x_150;
}
}
}
else
{
lean_dec(x_130);
goto block_128;
}
}
else
{
goto block_128;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Meta_whnfEasyCases___closed__10;
x_8 = l_panic___at___Lean_Meta_whnfCore_go_spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_FVarId_getDecl___redArg(x_9, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 4);
lean_inc(x_17);
x_18 = l_Lean_Meta_getConfig___redArg(x_2, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_54; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_54 = l_Lean_LocalDecl_isImplementationDetail(x_11);
lean_dec(x_11);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_20, 16);
lean_dec(x_20);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_57, x_9);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_dec(x_58);
lean_free_object(x_18);
lean_dec(x_1);
x_22 = x_2;
x_23 = x_56;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
goto block_47;
}
}
else
{
lean_free_object(x_18);
lean_dec(x_1);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_53;
}
}
else
{
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_1);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_53;
}
block_47:
{
if (x_23 == 0)
{
lean_object* x_27; 
lean_dec(x_9);
x_27 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_17, x_22, x_24, x_25, x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_24, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_29, 2);
x_33 = l_Lean_FVarIdSet_insert(x_32, x_9);
lean_ctor_set(x_29, 2, x_33);
x_34 = lean_st_ref_set(x_24, x_29, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_17, x_22, x_24, x_25, x_26, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_ctor_get(x_29, 3);
x_41 = lean_ctor_get(x_29, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_42 = l_Lean_FVarIdSet_insert(x_39, x_9);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_st_ref_set(x_24, x_43, x_30);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_17, x_22, x_24, x_25, x_26, x_45);
return x_46;
}
}
}
block_53:
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_48, sizeof(void*)*7 + 8);
x_22 = x_48;
x_23 = x_52;
x_24 = x_49;
x_25 = x_50;
x_26 = x_51;
goto block_47;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_88; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_88 = l_Lean_LocalDecl_isImplementationDetail(x_11);
lean_dec(x_11);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_59, 16);
lean_dec(x_59);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
x_92 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_91, x_9);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_60);
return x_93;
}
else
{
lean_dec(x_92);
lean_dec(x_1);
x_61 = x_2;
x_62 = x_90;
x_63 = x_3;
x_64 = x_4;
x_65 = x_5;
goto block_81;
}
}
else
{
lean_dec(x_1);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
goto block_87;
}
}
else
{
lean_dec(x_59);
lean_dec(x_1);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
goto block_87;
}
block_81:
{
if (x_62 == 0)
{
lean_object* x_66; 
lean_dec(x_9);
x_66 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_17, x_61, x_63, x_64, x_65, x_60);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_st_ref_take(x_63, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 4);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
x_76 = l_Lean_FVarIdSet_insert(x_72, x_9);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_74);
x_78 = lean_st_ref_set(x_63, x_77, x_69);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_17, x_61, x_63, x_64, x_65, x_79);
return x_80;
}
}
block_87:
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_82, sizeof(void*)*7 + 8);
x_61 = x_82;
x_62 = x_86;
x_63 = x_83;
x_64 = x_84;
x_65 = x_85;
goto block_81;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_10);
if (x_94 == 0)
{
return x_10;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 2:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f_spec__0___redArg(x_98, x_3, x_6);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
x_107 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_106, x_2, x_3, x_4, x_5, x_105);
return x_107;
}
}
case 3:
{
lean_object* x_108; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_6);
return x_108;
}
case 6:
{
lean_object* x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_6);
return x_109;
}
case 7:
{
lean_object* x_110; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_6);
return x_110;
}
case 9:
{
lean_object* x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_6);
return x_111;
}
case 10:
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0(x_112, x_2, x_3, x_4, x_5, x_6);
return x_113;
}
default: 
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; uint8_t x_129; uint8_t x_152; 
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___boxed), 7, 1);
lean_closure_set(x_114, 0, x_1);
x_152 = l_Lean_Expr_hasFVar(x_1);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = l_Lean_Expr_hasExprMVar(x_1);
x_129 = x_153;
goto block_151;
}
else
{
x_129 = x_152;
goto block_151;
}
block_125:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_117 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4;
x_118 = lean_box(x_115);
x_119 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1___boxed), 8, 3);
lean_closure_set(x_119, 0, x_117);
lean_closure_set(x_119, 1, x_1);
lean_closure_set(x_119, 2, x_118);
x_120 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
x_121 = lean_box(1);
x_122 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_;
x_123 = lean_unbox(x_121);
x_124 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___redArg(x_120, x_114, x_119, x_123, x_122, x_2, x_3, x_4, x_5, x_116);
return x_124;
}
block_128:
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_box(0);
x_127 = lean_unbox(x_126);
x_115 = x_127;
x_116 = x_6;
goto block_125;
}
block_151:
{
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_2, 6);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_131 = lean_box(1);
x_132 = lean_st_ref_get(x_3, x_6);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_1);
x_135 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_134);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 1);
x_140 = lean_ctor_get(x_136, 3);
lean_inc(x_140);
lean_dec(x_136);
x_141 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_140, x_138);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
lean_free_object(x_135);
x_142 = lean_unbox(x_131);
x_115 = x_142;
x_116 = x_139;
goto block_125;
}
else
{
lean_object* x_143; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
lean_ctor_set(x_135, 0, x_143);
return x_135;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_135);
x_146 = lean_ctor_get(x_136, 3);
lean_inc(x_146);
lean_dec(x_136);
x_147 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_146, x_144);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = lean_unbox(x_131);
x_115 = x_148;
x_116 = x_145;
goto block_125;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
return x_150;
}
}
}
else
{
lean_dec(x_130);
goto block_128;
}
}
else
{
goto block_128;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_nat_dec_eq(x_11, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_11, x_22);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_23);
x_24 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_24;
}
else
{
lean_object* x_25; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_13, x_6);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_4, 2);
x_29 = lean_ctor_get(x_4, 3);
x_30 = lean_ctor_get(x_4, 4);
x_31 = lean_ctor_get(x_4, 5);
x_32 = lean_ctor_get(x_4, 6);
x_33 = lean_ctor_get(x_4, 7);
x_34 = lean_ctor_get(x_4, 8);
x_35 = lean_ctor_get(x_4, 9);
x_36 = lean_ctor_get(x_4, 10);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_38 = lean_ctor_get(x_4, 11);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_40 = lean_ctor_get(x_4, 12);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_41 = lean_nat_dec_eq(x_29, x_30);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_29, x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_44, 2, x_28);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_30);
lean_ctor_set(x_44, 5, x_31);
lean_ctor_set(x_44, 6, x_32);
lean_ctor_set(x_44, 7, x_33);
lean_ctor_set(x_44, 8, x_34);
lean_ctor_set(x_44, 9, x_35);
lean_ctor_set(x_44, 10, x_36);
lean_ctor_set(x_44, 11, x_38);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*13, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 1, x_39);
x_45 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0(x_1, x_2, x_3, x_44, x_5, x_6);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_31, x_6);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProjOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Environment_getProjectionStructureName_x3f(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_1(x_2, x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_free_object(x_13);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_25, x_3, x_4, x_5, x_6, x_16);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Environment_getProjectionStructureName_x3f(x_29, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_apply_1(x_2, x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_39, x_3, x_4, x_5, x_6, x_28);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WHNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10892u);
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_10892_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_9 = lean_unbox(x_3);
x_10 = l_Lean_registerTraceClass(x_8, x_9, x_4, x_7);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GetUnfoldableConst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchPatternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_smartUnfoldingSuffix___closed__0 = _init_l_Lean_Meta_smartUnfoldingSuffix___closed__0();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix___closed__0);
l_Lean_Meta_smartUnfoldingSuffix = _init_l_Lean_Meta_smartUnfoldingSuffix();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_36_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_36_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_36_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_smartUnfolding = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_smartUnfolding);
lean_dec_ref(res);
}l_Lean_Meta_markSmartUnfoldingMatch___closed__0 = _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__0();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatch___closed__0);
l_Lean_Meta_markSmartUnfoldingMatch___closed__1 = _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatch___closed__1);
l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0 = _init_l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__0);
l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1 = _init_l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatchAlt___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___redArg___closed__0);
l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0 = _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__0);
l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1 = _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__1);
l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2 = _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__2);
l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3 = _init_l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_____private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure_spec__0___closed__3);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__0);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__3);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isWFRec___closed__4);
l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___redArg___closed__0();
l_Lean_Meta_whnfEasyCases___closed__0 = _init_l_Lean_Meta_whnfEasyCases___closed__0();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__0);
l_Lean_Meta_whnfEasyCases___closed__1 = _init_l_Lean_Meta_whnfEasyCases___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__1);
l_Lean_Meta_whnfEasyCases___closed__2 = _init_l_Lean_Meta_whnfEasyCases___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__2);
l_Lean_Meta_whnfEasyCases___closed__3 = _init_l_Lean_Meta_whnfEasyCases___closed__3();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__3);
l_Lean_Meta_whnfEasyCases___closed__4 = _init_l_Lean_Meta_whnfEasyCases___closed__4();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__4);
l_Lean_Meta_whnfEasyCases___closed__5 = _init_l_Lean_Meta_whnfEasyCases___closed__5();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__5);
l_Lean_Meta_whnfEasyCases___closed__6 = _init_l_Lean_Meta_whnfEasyCases___closed__6();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__6);
l_Lean_Meta_whnfEasyCases___closed__7 = _init_l_Lean_Meta_whnfEasyCases___closed__7();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__7);
l_Lean_Meta_whnfEasyCases___closed__8 = _init_l_Lean_Meta_whnfEasyCases___closed__8();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__8);
l_Lean_Meta_whnfEasyCases___closed__9 = _init_l_Lean_Meta_whnfEasyCases___closed__9();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__9);
l_Lean_Meta_whnfEasyCases___closed__10 = _init_l_Lean_Meta_whnfEasyCases___closed__10();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___closed__10);
l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__0);
l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__0___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldNestedDIte___lam__2___closed__0);
l_Lean_Meta_canUnfoldAtMatcher___closed__0 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__0();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__0);
l_Lean_Meta_canUnfoldAtMatcher___closed__1 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__1();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__1);
l_Lean_Meta_canUnfoldAtMatcher___closed__2 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__2();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__2);
l_Lean_Meta_canUnfoldAtMatcher___closed__3 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__3();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__3);
l_Lean_Meta_canUnfoldAtMatcher___closed__4 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__4();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__4);
l_Lean_Meta_canUnfoldAtMatcher___closed__5 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__5();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__5);
l_Lean_Meta_canUnfoldAtMatcher___closed__6 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__6();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__6);
l_Lean_Meta_canUnfoldAtMatcher___closed__7 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__7();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__7);
l_Lean_Meta_canUnfoldAtMatcher___closed__8 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__8();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__8);
l_Lean_Meta_canUnfoldAtMatcher___closed__9 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__9();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__9);
l_Lean_Meta_canUnfoldAtMatcher___closed__10 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__10();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__10);
l_Lean_Meta_canUnfoldAtMatcher___closed__11 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__11();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__11);
l_Lean_Meta_canUnfoldAtMatcher___closed__12 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__12();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__12);
l_Lean_Meta_canUnfoldAtMatcher___closed__13 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__13();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__13);
l_Lean_Meta_canUnfoldAtMatcher___closed__14 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__14();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__14);
l_Lean_Meta_canUnfoldAtMatcher___closed__15 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__15();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__15);
l_Lean_Meta_canUnfoldAtMatcher___closed__16 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__16();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__16);
l_Lean_Meta_canUnfoldAtMatcher___closed__17 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__17();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__17);
l_Lean_Meta_canUnfoldAtMatcher___closed__18 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__18();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__18);
l_Lean_Meta_canUnfoldAtMatcher___closed__19 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__19();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__19);
l_Lean_Meta_canUnfoldAtMatcher___closed__20 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__20();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__20);
l_Lean_Meta_canUnfoldAtMatcher___closed__21 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__21();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__21);
l_Lean_Meta_canUnfoldAtMatcher___closed__22 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__22();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__22);
l_Lean_Meta_canUnfoldAtMatcher___closed__23 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__23();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__23);
l_Lean_Meta_canUnfoldAtMatcher___closed__24 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__24();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__24);
l_Lean_Meta_canUnfoldAtMatcher___closed__25 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__25();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__25);
l_Lean_Meta_canUnfoldAtMatcher___closed__26 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__26();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__26);
l_Lean_Meta_canUnfoldAtMatcher___closed__27 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__27();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__27);
l_Lean_Meta_canUnfoldAtMatcher___closed__28 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__28();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__28);
l_Lean_Meta_canUnfoldAtMatcher___closed__29 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__29();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__29);
l_Lean_Meta_canUnfoldAtMatcher___closed__30 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__30();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__30);
l_Lean_Meta_canUnfoldAtMatcher___closed__31 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__31();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__31);
l_Lean_Meta_canUnfoldAtMatcher___closed__32 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__32();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__32);
l_Lean_Meta_canUnfoldAtMatcher___closed__33 = _init_l_Lean_Meta_canUnfoldAtMatcher___closed__33();
lean_mark_persistent(l_Lean_Meta_canUnfoldAtMatcher___closed__33);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__0);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__1();
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfMatcher___closed__2);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__0);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__1);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__2);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__3);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__4);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfCore_go_spec__2_spec__2___closed__5);
l_Lean_Meta_unfoldProjInst_x3f___closed__0 = _init_l_Lean_Meta_unfoldProjInst_x3f___closed__0();
l_Lean_Meta_unfoldDefinition_x3f___closed__0 = _init_l_Lean_Meta_unfoldDefinition_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition_x3f___closed__0);
l_Lean_Meta_unfoldDefinition___closed__0 = _init_l_Lean_Meta_unfoldDefinition___closed__0();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__0);
l_Lean_Meta_unfoldDefinition___closed__1 = _init_l_Lean_Meta_unfoldDefinition___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__1);
l_Lean_Meta_unfoldDefinition___closed__2 = _init_l_Lean_Meta_unfoldDefinition___closed__2();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__2);
l_Lean_Meta_reduceBoolNativeUnsafe___closed__0 = _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__0();
lean_mark_persistent(l_Lean_Meta_reduceBoolNativeUnsafe___closed__0);
l_Lean_Meta_reduceBoolNativeUnsafe___closed__1 = _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceBoolNativeUnsafe___closed__1);
l_Lean_Meta_reduceNatNativeUnsafe___closed__0 = _init_l_Lean_Meta_reduceNatNativeUnsafe___closed__0();
lean_mark_persistent(l_Lean_Meta_reduceNatNativeUnsafe___closed__0);
l_Lean_Meta_reduceNative_x3f___closed__0 = _init_l_Lean_Meta_reduceNative_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__0);
l_Lean_Meta_reduceNative_x3f___closed__1 = _init_l_Lean_Meta_reduceNative_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__1);
l_Lean_Meta_reduceNative_x3f___closed__2 = _init_l_Lean_Meta_reduceNative_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__2);
l_Lean_Meta_reduceNative_x3f___closed__3 = _init_l_Lean_Meta_reduceNative_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__3);
l_Lean_Meta_reduceNative_x3f___closed__4 = _init_l_Lean_Meta_reduceNative_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__4);
l_Lean_Meta_reduceNative_x3f___closed__5 = _init_l_Lean_Meta_reduceNative_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__5);
l_Lean_Meta_reduceNative_x3f___closed__6 = _init_l_Lean_Meta_reduceNative_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__6);
l_Lean_Meta_reduceNative_x3f___closed__7 = _init_l_Lean_Meta_reduceNative_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__7);
l_Lean_Meta_reduceNative_x3f___closed__8 = _init_l_Lean_Meta_reduceNative_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__8);
l_Lean_Meta_reduceNative_x3f___closed__9 = _init_l_Lean_Meta_reduceNative_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__9);
l_Lean_Meta_withNatValue___redArg___closed__0 = _init_l_Lean_Meta_withNatValue___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_withNatValue___redArg___closed__0);
l_Lean_Meta_reduceBinNatOp___closed__0 = _init_l_Lean_Meta_reduceBinNatOp___closed__0();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__0);
l_Lean_Meta_reduceBinNatOp___closed__1 = _init_l_Lean_Meta_reduceBinNatOp___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__1);
l_Lean_Meta_reduceBinNatOp___closed__2 = _init_l_Lean_Meta_reduceBinNatOp___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__2);
l_Lean_Meta_reduceBinNatOp___closed__3 = _init_l_Lean_Meta_reduceBinNatOp___closed__3();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__3);
l_Lean_Meta_reduceBinNatOp___closed__4 = _init_l_Lean_Meta_reduceBinNatOp___closed__4();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__4);
l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__0();
l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__1);
l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_reducePow_spec__1___closed__2);
l_Lean_Meta_reducePow___closed__0 = _init_l_Lean_Meta_reducePow___closed__0();
lean_mark_persistent(l_Lean_Meta_reducePow___closed__0);
l_Lean_Meta_reducePow___closed__1 = _init_l_Lean_Meta_reducePow___closed__1();
lean_mark_persistent(l_Lean_Meta_reducePow___closed__1);
l_Lean_Meta_reduceNat_x3f___closed__0 = _init_l_Lean_Meta_reduceNat_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__0);
l_Lean_Meta_reduceNat_x3f___closed__1 = _init_l_Lean_Meta_reduceNat_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__1);
l_Lean_Meta_reduceNat_x3f___closed__2 = _init_l_Lean_Meta_reduceNat_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__2);
l_Lean_Meta_reduceNat_x3f___closed__3 = _init_l_Lean_Meta_reduceNat_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__3);
l_Lean_Meta_reduceNat_x3f___closed__4 = _init_l_Lean_Meta_reduceNat_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__4);
l_Lean_Meta_reduceNat_x3f___closed__5 = _init_l_Lean_Meta_reduceNat_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__5);
l_Lean_Meta_reduceNat_x3f___closed__6 = _init_l_Lean_Meta_reduceNat_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__6);
l_Lean_Meta_reduceNat_x3f___closed__7 = _init_l_Lean_Meta_reduceNat_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__7);
l_Lean_Meta_reduceNat_x3f___closed__8 = _init_l_Lean_Meta_reduceNat_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__8);
l_Lean_Meta_reduceNat_x3f___closed__9 = _init_l_Lean_Meta_reduceNat_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__9);
l_Lean_Meta_reduceNat_x3f___closed__10 = _init_l_Lean_Meta_reduceNat_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__10);
l_Lean_Meta_reduceNat_x3f___closed__11 = _init_l_Lean_Meta_reduceNat_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__11);
l_Lean_Meta_reduceNat_x3f___closed__12 = _init_l_Lean_Meta_reduceNat_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__12);
l_Lean_Meta_reduceNat_x3f___closed__13 = _init_l_Lean_Meta_reduceNat_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__13);
l_Lean_Meta_reduceNat_x3f___closed__14 = _init_l_Lean_Meta_reduceNat_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__14);
l_Lean_Meta_reduceNat_x3f___closed__15 = _init_l_Lean_Meta_reduceNat_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__15);
l_Lean_Meta_reduceNat_x3f___closed__16 = _init_l_Lean_Meta_reduceNat_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__16);
l_Lean_Meta_reduceNat_x3f___closed__17 = _init_l_Lean_Meta_reduceNat_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__17);
l_Lean_Meta_reduceNat_x3f___closed__18 = _init_l_Lean_Meta_reduceNat_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__18);
l_Lean_Meta_reduceNat_x3f___closed__19 = _init_l_Lean_Meta_reduceNat_x3f___closed__19();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__19);
l_Lean_Meta_reduceNat_x3f___closed__20 = _init_l_Lean_Meta_reduceNat_x3f___closed__20();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__20);
l_Lean_Meta_reduceNat_x3f___closed__21 = _init_l_Lean_Meta_reduceNat_x3f___closed__21();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__21);
l_Lean_Meta_reduceNat_x3f___closed__22 = _init_l_Lean_Meta_reduceNat_x3f___closed__22();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__22);
l_Lean_Meta_reduceNat_x3f___closed__23 = _init_l_Lean_Meta_reduceNat_x3f___closed__23();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__23);
l_Lean_Meta_reduceNat_x3f___closed__24 = _init_l_Lean_Meta_reduceNat_x3f___closed__24();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__24);
l_Lean_Meta_reduceNat_x3f___closed__25 = _init_l_Lean_Meta_reduceNat_x3f___closed__25();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__25);
l_Lean_Meta_reduceNat_x3f___closed__26 = _init_l_Lean_Meta_reduceNat_x3f___closed__26();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__26);
l_Lean_Meta_reduceNat_x3f___closed__27 = _init_l_Lean_Meta_reduceNat_x3f___closed__27();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__27);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__0);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___redArg___closed__1);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__0);
l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1 = _init_l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfEasyCases___at___Lean_Meta_whnfImp_spec__0_spec__0___lam__0___closed__1);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_WHNF___hyg_10892_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_WHNF___hyg_10892_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_10892_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
