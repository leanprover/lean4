// Lean compiler output
// Module: Lean.Meta.WHNF
// Imports: Init Lean.ToExpr Lean.AuxRecursor Lean.ProjFns Lean.Meta.Basic Lean.Meta.LevelDefEq Lean.Meta.GetConst Lean.Meta.Match.MatcherInfo
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
lean_object* lean_string_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3(lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__3;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__16;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__6;
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__5;
extern lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__14;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__23;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__7;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__24;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__10;
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__3;
LEAN_EXPORT lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldigMatchAlt(lean_object*);
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object*);
uint8_t l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__16;
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__14;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBoolNative___rarg___closed__1;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingSuffix;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__7;
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatch___closed__1;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2(lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__18;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldingMatch___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__3;
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatch(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__10;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_toCtorIfLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2(lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1;
lean_object* l_Lean_Meta_getDelayedAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_project_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f___boxed(lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__12;
lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
static lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__3;
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___boxed(lean_object**);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__9;
static lean_object* l_Lean_Meta_smartUnfoldingSuffix___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2;
static lean_object* l_Lean_Meta_unfoldDefinition___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBoolNative___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__10;
static lean_object* l_Lean_Meta_whnfImp___closed__1;
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__12;
uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__17;
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_6085_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
static lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1;
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldDefinition___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfolding;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_smartUnfolding___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__21;
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceMatcher_x3f___closed__1;
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__2;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__11;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__4;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
lean_object* lean_synth_pending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__12;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__17;
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__11;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__4;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
static lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
static lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___at_Lean_Environment_getProjectionFnInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__8;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__1;
static lean_object* l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_toCtorIfLit___closed__19;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object*, size_t, size_t);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__2;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__15;
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__18;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
static lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__5;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__22;
static lean_object* l_Lean_Meta_whnfImp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__4;
static lean_object* l_Lean_Meta_reduceNative_x3f___closed__13;
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___closed__1;
static lean_object* l_Lean_Meta_toCtorIfLit___closed__25;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceBinNatOp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
static lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1;
static lean_object* l_Lean_Meta_whnfEasyCases___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldDefinition___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3;
static lean_object* _init_l_Lean_Meta_smartUnfoldingSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_sunfold");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_smartUnfoldingSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfoldingSuffix___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_smartUnfoldingSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("smartUnfolding");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("when computing weak head normal form, use auxiliary definition created for functions defined by structural recursion");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_smartUnfolding___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sunfoldMatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_markSmartUnfoldingMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldingMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatch___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldingMatch___closed__2;
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
static lean_object* _init_l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sunfoldMatchAlt");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markSmartUnfoldigMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingMatchAlt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_isAuxDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_10);
x_11 = lean_is_aux_recursor(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = l_Lean_noConfusionExt;
x_13 = l_Lean_TagDeclarationExtension_isTagged(x_12, x_10, x_1);
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
lean_inc(x_19);
x_20 = lean_is_aux_recursor(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_noConfusionExt;
x_22 = l_Lean_TagDeclarationExtension_isTagged(x_21, x_19, x_1);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_1);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Meta_getConst_x3f(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_2, x_14, x_4, x_5, x_6, x_7, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_apply_7(x_3, x_17, x_10, x_4, x_5, x_6, x_7, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_6(x_2, x_23, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_getConstNoEx_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_free_object(x_8);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_ctor_set(x_8, 0, x_27);
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
lean_ctor_set(x_8, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_free_object(x_8);
lean_dec(x_16);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_7, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
if (lean_obj_tag(x_37) == 5)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 4);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_45 = x_7;
} else {
 lean_dec_ref(x_7);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_50 = x_7;
} else {
 lean_dec_ref(x_7);
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
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(x_9, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = l_Lean_mkConst(x_22, x_10);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux(x_1, x_24);
x_26 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_27, x_29);
x_31 = l_Array_shrink___rarg(x_30, x_2);
x_32 = l_Lean_mkAppN(x_23, x_31);
lean_ctor_set(x_12, 0, x_32);
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_mkConst(x_33, x_10);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux(x_1, x_35);
x_37 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_38, x_40);
x_42 = l_Array_shrink___rarg(x_41, x_2);
x_43 = l_Lean_mkAppN(x_34, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_11, 0, x_44);
return x_11;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_47 = x_12;
} else {
 lean_dec_ref(x_12);
 x_47 = lean_box(0);
}
x_48 = l_Lean_mkConst(x_46, x_10);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Expr_getAppNumArgsAux(x_1, x_49);
x_51 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_50);
x_52 = lean_mk_array(x_50, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_50, x_53);
lean_dec(x_50);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_52, x_54);
x_56 = l_Array_shrink___rarg(x_55, x_2);
x_57 = l_Lean_mkAppN(x_48, x_56);
if (lean_is_scalar(x_47)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_47;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_8);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
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
static lean_object* _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Char");
return x_1;
}
}
static lean_object* _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofNat");
return x_1;
}
}
static lean_object* _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2;
x_2 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = lean_uint32_to_nat(x_6);
x_8 = l_Lean_mkNatLit(x_7);
x_9 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5;
x_10 = l_Lean_mkApp(x_9, x_8);
lean_inc(x_2);
x_11 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_1, x_2, x_5);
x_12 = l_Lean_mkAppB(x_2, x_10, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__10;
x_2 = l_Lean_Meta_toCtorIfLit___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__16;
x_2 = l_Lean_Meta_toCtorIfLit___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__18;
x_2 = l_Lean_Meta_toCtorIfLit___closed__19;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__20;
x_2 = l_Lean_Meta_toCtorIfLit___closed__14;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cons");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__16;
x_2 = l_Lean_Meta_toCtorIfLit___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__23;
x_2 = l_Lean_Meta_toCtorIfLit___closed__19;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__24;
x_2 = l_Lean_Meta_toCtorIfLit___closed__14;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toCtorIfLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = l_Lean_Meta_toCtorIfLit___closed__5;
x_10 = l_Lean_mkApp(x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_Meta_toCtorIfLit___closed__8;
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_string_data(x_12);
x_14 = l_Lean_Meta_toCtorIfLit___closed__21;
x_15 = l_Lean_Meta_toCtorIfLit___closed__25;
x_16 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_14, x_15, x_13);
x_17 = l_Lean_Meta_toCtorIfLit___closed__13;
x_18 = l_Lean_mkApp(x_17, x_16);
return x_18;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_find_x3f___rarg(x_5, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(x_1, x_2);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
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
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_instantiateMVars(x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_79 = l_Lean_Expr_getAppFn(x_16);
x_80 = l_Lean_RecursorVal_getInduct(x_1);
x_81 = l_Lean_Expr_isConstOf(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
lean_ctor_set(x_14, 0, x_82);
return x_14;
}
else
{
uint8_t x_83; 
x_83 = l_Lean_Expr_hasExprMVar(x_16);
if (x_83 == 0)
{
lean_object* x_84; 
lean_free_object(x_14);
x_84 = lean_box(0);
x_18 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Expr_getAppNumArgsAux(x_16, x_85);
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_86);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_86, x_89);
lean_dec(x_86);
lean_inc(x_16);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_16, x_88, x_90);
x_92 = lean_ctor_get(x_1, 2);
lean_inc(x_92);
x_93 = lean_array_get_size(x_91);
x_94 = l_Array_toSubarray___rarg(x_91, x_92, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 2);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_free_object(x_14);
x_99 = lean_box(0);
x_18 = x_99;
goto block_78;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_array_get_size(x_95);
x_101 = lean_nat_dec_le(x_97, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_free_object(x_14);
x_102 = lean_box(0);
x_18 = x_102;
goto block_78;
}
else
{
size_t x_103; size_t x_104; uint8_t x_105; 
x_103 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_104 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_105 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_95, x_103, x_104);
lean_dec(x_95);
if (x_105 == 0)
{
lean_object* x_106; 
lean_free_object(x_14);
x_106 = lean_box(0);
x_18 = x_106;
goto block_78;
}
else
{
lean_object* x_107; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_box(0);
lean_ctor_set(x_14, 0, x_107);
return x_14;
}
}
}
}
}
block_78:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_16);
x_20 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_16, x_19, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_31 = lean_infer_type(x_30, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_isExprDefEq(x_16, x_32, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_21);
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
lean_ctor_set(x_34, 0, x_21);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_21);
lean_dec(x_30);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_21, 0);
lean_inc(x_55);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_56 = lean_infer_type(x_55, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_isExprDefEq(x_16, x_57, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_55);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_108 = lean_ctor_get(x_14, 0);
x_109 = lean_ctor_get(x_14, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_14);
x_144 = l_Lean_Expr_getAppFn(x_108);
x_145 = l_Lean_RecursorVal_getInduct(x_1);
x_146 = l_Lean_Expr_isConstOf(x_144, x_145);
lean_dec(x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_109);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasExprMVar(x_108);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_110 = x_150;
goto block_143;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Lean_Expr_getAppNumArgsAux(x_108, x_151);
x_153 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_152);
x_154 = lean_mk_array(x_152, x_153);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_sub(x_152, x_155);
lean_dec(x_152);
lean_inc(x_108);
x_157 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_108, x_154, x_156);
x_158 = lean_ctor_get(x_1, 2);
lean_inc(x_158);
x_159 = lean_array_get_size(x_157);
x_160 = l_Array_toSubarray___rarg(x_157, x_158, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_nat_dec_lt(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
x_165 = lean_box(0);
x_110 = x_165;
goto block_143;
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_array_get_size(x_161);
x_167 = lean_nat_dec_le(x_163, x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
x_168 = lean_box(0);
x_110 = x_168;
goto block_143;
}
else
{
size_t x_169; size_t x_170; uint8_t x_171; 
x_169 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_170 = lean_usize_of_nat(x_163);
lean_dec(x_163);
x_171 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_161, x_169, x_170);
lean_dec(x_161);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_box(0);
x_110 = x_172;
goto block_143;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_109);
return x_174;
}
}
}
}
}
block_143:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_110);
x_111 = lean_ctor_get(x_1, 2);
lean_inc(x_111);
lean_dec(x_1);
lean_inc(x_108);
x_112 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_108, x_111, x_3, x_4, x_5, x_6, x_109);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_dec(x_112);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_119);
x_121 = lean_infer_type(x_119, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Meta_isExprDefEq(x_108, x_122, x_3, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
lean_dec(x_119);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_132 = x_124;
} else {
 lean_dec_ref(x_124);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_120;
}
lean_ctor_set(x_133, 0, x_119);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_120);
lean_dec(x_119);
x_135 = lean_ctor_get(x_124, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_124, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_ctor_get(x_121, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_121, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_141 = x_121;
} else {
 lean_dec_ref(x_121);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_14);
if (x_175 == 0)
{
return x_14;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_14, 0);
x_177 = lean_ctor_get(x_14, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_14);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_11);
if (x_179 == 0)
{
return x_11;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_11, 0);
x_181 = lean_ctor_get(x_11, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_11);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_8);
if (x_183 == 0)
{
return x_8;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_8, 0);
x_185 = lean_ctor_get(x_8, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_8);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Meta_toCtorIfLit(x_8);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_6(x_2, x_17, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux(x_15, x_20);
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_23, x_25);
x_27 = l_List_lengthTRAux___rarg(x_3, x_20);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_List_lengthTRAux___rarg(x_29, x_20);
x_31 = lean_nat_dec_eq(x_27, x_30);
lean_dec(x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_apply_6(x_2, x_32, x_10, x_11, x_12, x_13, x_14);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_19, 2);
lean_inc(x_34);
x_35 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_29, x_3, x_34);
lean_dec(x_29);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 4);
lean_inc(x_37);
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_41 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_40, x_4, x_20, x_35);
lean_dec(x_40);
x_42 = lean_array_get_size(x_26);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_nat_sub(x_42, x_43);
lean_dec(x_43);
x_45 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_42, x_26, x_44, x_41);
lean_dec(x_26);
lean_dec(x_42);
x_46 = lean_nat_add(x_5, x_24);
x_47 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_6, x_4, x_46, x_45);
x_48 = lean_apply_6(x_7, x_47, x_10, x_11, x_12, x_13, x_14);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_4, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_3, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = lean_whnf(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_19, x_21, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(x_1, x_23, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_23, x_28, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_31, x_32, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_23);
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
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
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
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_12 = lean_box(x_11);
switch (lean_obj_tag(x_12)) {
case 2:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_4, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_3, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_whnf(x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_getConstNoEx_x3f(x_26, x_6, x_7, x_8, x_9, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_5);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_apply_6(x_4, x_30, x_6, x_7, x_8, x_9, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
x_35 = lean_box(x_34);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l_Lean_instInhabitedExpr;
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_array_get(x_37, x_3, x_38);
x_40 = l_Lean_mkApp(x_39, x_25);
x_41 = lean_unsigned_to_nat(6u);
x_42 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_13, x_3, x_41, x_40);
lean_dec(x_13);
x_43 = lean_apply_6(x_5, x_42, x_6, x_7, x_8, x_9, x_36);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_5);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_box(0);
x_46 = lean_apply_6(x_4, x_45, x_6, x_7, x_8, x_9, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_5);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_dec(x_27);
x_48 = lean_box(0);
x_49 = lean_apply_6(x_4, x_48, x_6, x_7, x_8, x_9, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_dec(x_19);
x_51 = lean_box(0);
x_52 = lean_apply_6(x_4, x_51, x_6, x_7, x_8, x_9, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_box(0);
x_55 = lean_apply_6(x_4, x_54, x_6, x_7, x_8, x_9, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
x_56 = lean_ctor_get(x_19, 1);
lean_inc(x_56);
lean_dec(x_19);
x_57 = lean_box(0);
x_58 = lean_apply_6(x_4, x_57, x_6, x_7, x_8, x_9, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_dec(x_19);
x_60 = lean_box(0);
x_61 = lean_apply_6(x_4, x_60, x_6, x_7, x_8, x_9, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_array_get_size(x_3);
x_67 = lean_unsigned_to_nat(4u);
x_68 = lean_nat_dec_lt(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_5);
x_69 = lean_box(0);
x_70 = lean_apply_6(x_4, x_69, x_6, x_7, x_8, x_9, x_10);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_array_fget(x_3, x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = lean_whnf(x_71, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 5)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 5)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 5)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 4)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Lean_Meta_getConstNoEx_x3f(x_79, x_6, x_7, x_8, x_9, x_77);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
lean_dec(x_66);
lean_dec(x_5);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
x_84 = lean_apply_6(x_4, x_83, x_6, x_7, x_8, x_9, x_82);
return x_84;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
if (lean_obj_tag(x_85) == 4)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
x_88 = lean_box(x_87);
if (lean_obj_tag(x_88) == 1)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_dec(x_80);
x_90 = l_Lean_instInhabitedExpr;
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_array_get(x_90, x_3, x_91);
x_93 = l_Lean_mkApp(x_92, x_78);
x_94 = lean_unsigned_to_nat(5u);
x_95 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_66, x_3, x_94, x_93);
lean_dec(x_66);
x_96 = lean_apply_6(x_5, x_95, x_6, x_7, x_8, x_9, x_89);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_88);
lean_dec(x_78);
lean_dec(x_66);
lean_dec(x_5);
x_97 = lean_ctor_get(x_80, 1);
lean_inc(x_97);
lean_dec(x_80);
x_98 = lean_box(0);
x_99 = lean_apply_6(x_4, x_98, x_6, x_7, x_8, x_9, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_85);
lean_dec(x_78);
lean_dec(x_66);
lean_dec(x_5);
x_100 = lean_ctor_get(x_80, 1);
lean_inc(x_100);
lean_dec(x_80);
x_101 = lean_box(0);
x_102 = lean_apply_6(x_4, x_101, x_6, x_7, x_8, x_9, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_5);
x_103 = lean_ctor_get(x_72, 1);
lean_inc(x_103);
lean_dec(x_72);
x_104 = lean_box(0);
x_105 = lean_apply_6(x_4, x_104, x_6, x_7, x_8, x_9, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_5);
x_106 = lean_ctor_get(x_72, 1);
lean_inc(x_106);
lean_dec(x_72);
x_107 = lean_box(0);
x_108 = lean_apply_6(x_4, x_107, x_6, x_7, x_8, x_9, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_5);
x_109 = lean_ctor_get(x_72, 1);
lean_inc(x_109);
lean_dec(x_72);
x_110 = lean_box(0);
x_111 = lean_apply_6(x_4, x_110, x_6, x_7, x_8, x_9, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_5);
x_112 = lean_ctor_get(x_72, 1);
lean_inc(x_112);
lean_dec(x_72);
x_113 = lean_box(0);
x_114 = lean_apply_6(x_4, x_113, x_6, x_7, x_8, x_9, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_72);
if (x_115 == 0)
{
return x_72;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_72, 0);
x_117 = lean_ctor_get(x_72, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_72);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
default: 
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_12);
lean_dec(x_5);
x_119 = lean_box(0);
x_120 = lean_apply_6(x_4, x_119, x_6, x_7, x_8, x_9, x_10);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_RecursorVal_getMajorIdx(x_1);
lean_dec(x_1);
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_10);
lean_dec(x_10);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_whnf(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_getStuckMVar_x3f(x_17, x_4, x_5, x_6, x_7, x_18);
return x_19;
}
else
{
uint8_t x_20; 
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
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 2)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_1 = x_8;
x_6 = x_17;
goto _start;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 5:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = l_Lean_Expr_getAppFn(x_23);
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Lean_Meta_getConstNoEx_x3f(x_28, x_2, x_3, x_4, x_5, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
switch (lean_obj_tag(x_38)) {
case 4:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Expr_getAppNumArgsAux(x_1, x_41);
x_43 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_42);
x_44 = lean_mk_array(x_42, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_42, x_45);
lean_dec(x_42);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_44, x_46);
x_48 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_40, x_29, x_47, x_2, x_3, x_4, x_5, x_39);
return x_48;
}
case 7:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Expr_getAppNumArgsAux(x_1, x_51);
x_53 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_54, x_56);
x_58 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_50, x_29, x_57, x_2, x_3, x_4, x_5, x_49);
return x_58;
}
default: 
{
uint8_t x_59; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_30);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_30, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_30, 0, x_61);
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_dec(x_30);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_6);
return x_66;
}
}
}
case 10:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_1 = x_67;
goto _start;
}
case 11:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_70 = lean_whnf(x_69, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_1 = x_71;
x_6 = x_72;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
default: 
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_6);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_10 = lean_box(x_9);
switch (lean_obj_tag(x_10)) {
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_3, x_12);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_whnf(x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_getStuckMVar_x3f(x_18, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_array_get_size(x_3);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_dec_lt(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_3, x_26);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = lean_whnf(x_30, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_getStuckMVar_x3f(x_32, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = l_Lean_Meta_whnfEasyCases(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.WHNF");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.whnfEasyCases");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__2;
x_2 = l_Lean_Meta_whnfEasyCases___closed__3;
x_3 = lean_unsigned_to_nat(223u);
x_4 = lean_unsigned_to_nat(26u);
x_5 = l_Lean_Meta_whnfEasyCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Lean_Meta_whnfEasyCases___closed__1;
x_9 = l_Lean_Meta_whnfEasyCases___closed__5;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalDecl(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
lean_dec(x_14);
x_22 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
if (x_21 == 0)
{
lean_object* x_54; 
lean_free_object(x_22);
lean_dec(x_1);
x_54 = lean_box(0);
x_26 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_24, 6);
if (x_55 == 0)
{
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_56; 
lean_free_object(x_22);
lean_dec(x_1);
x_56 = lean_box(0);
x_26 = x_56;
goto block_53;
}
}
block_53:
{
uint8_t x_27; 
lean_dec(x_26);
x_27 = lean_ctor_get_uint8(x_24, 7);
lean_dec(x_24);
if (x_27 == 0)
{
lean_dec(x_12);
x_1 = x_20;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_st_ref_get(x_6, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_32, 2);
x_36 = l_Lean_Meta_whnfEasyCases___closed__6;
x_37 = lean_box(0);
x_38 = l_Std_RBNode_insert___rarg(x_36, x_35, x_12, x_37);
lean_ctor_set(x_32, 2, x_38);
x_39 = lean_st_ref_set(x_4, x_32, x_33);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_1 = x_20;
x_7 = x_40;
goto _start;
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
x_46 = l_Lean_Meta_whnfEasyCases___closed__6;
x_47 = lean_box(0);
x_48 = l_Std_RBNode_insert___rarg(x_46, x_44, x_12, x_47);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_45);
x_50 = lean_st_ref_set(x_4, x_49, x_33);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_1 = x_20;
x_7 = x_51;
goto _start;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
if (x_21 == 0)
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_box(0);
x_59 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = lean_ctor_get_uint8(x_57, 6);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_57);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_58);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_1);
x_83 = lean_box(0);
x_59 = x_83;
goto block_79;
}
}
block_79:
{
uint8_t x_60; 
lean_dec(x_59);
x_60 = lean_ctor_get_uint8(x_57, 7);
lean_dec(x_57);
if (x_60 == 0)
{
lean_dec(x_12);
x_1 = x_20;
x_7 = x_58;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_st_ref_get(x_6, x_58);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_take(x_4, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
x_72 = l_Lean_Meta_whnfEasyCases___closed__6;
x_73 = lean_box(0);
x_74 = l_Std_RBNode_insert___rarg(x_72, x_69, x_12, x_73);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 4, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_70);
x_76 = lean_st_ref_set(x_4, x_75, x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_1 = x_20;
x_7 = x_77;
goto _start;
}
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_13);
if (x_84 == 0)
{
return x_13;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_13, 0);
x_86 = lean_ctor_get(x_13, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_13);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 2:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = l_Lean_Meta_getExprMVarAssignment_x3f(x_88, x_3, x_4, x_5, x_6, x_7);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
lean_ctor_set(x_89, 0, x_1);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
lean_dec(x_90);
x_1 = x_96;
x_7 = x_95;
goto _start;
}
}
case 4:
{
lean_object* x_98; 
x_98 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_98;
}
case 5:
{
lean_object* x_99; 
x_99 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_99;
}
case 8:
{
lean_object* x_100; 
x_100 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_100;
}
case 10:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec(x_1);
x_1 = x_101;
goto _start;
}
case 11:
{
lean_object* x_103; 
x_103 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_103;
}
default: 
{
lean_object* x_104; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_7);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_ConstantInfo_levelParams(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_List_lengthTRAux___rarg(x_5, x_6);
lean_dec(x_5);
x_8 = l_List_lengthTRAux___rarg(x_2, x_6);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_instantiate_value_lparams(x_1, x_2);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_ConstantInfo_levelParams(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthTRAux___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthTRAux___rarg(x_2, x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_instantiate_value_lparams(x_1, x_2);
x_14 = l_Lean_Expr_betaRev(x_13, x_3);
lean_dec(x_13);
x_15 = lean_apply_1(x_5, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_10, x_1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = x_11 < x_10;
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_9, x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_12, 1);
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = lean_expr_eqv(x_7, x_20);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_free_object(x_12);
x_25 = lean_box(0);
lean_inc(x_8);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1(x_8, x_22, x_25, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = x_11 + x_30;
x_11 = x_31;
x_12 = x_29;
x_17 = x_28;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_2, x_22);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux(x_6, x_35);
lean_inc(x_36);
x_37 = lean_mk_array(x_36, x_1);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_36, x_38);
lean_dec(x_36);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_6, x_37, x_39);
x_41 = l_Lean_mkAppN(x_34, x_40);
x_42 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_43 = l_Array_ofSubarray___rarg(x_42);
x_44 = l_Lean_mkAppN(x_41, x_43);
x_45 = l_Lean_Expr_headBeta(x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_12, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_17);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_dec(x_12);
x_50 = lean_expr_eqv(x_7, x_20);
lean_dec(x_20);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_51 = lean_box(0);
lean_inc(x_8);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1(x_8, x_49, x_51, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = 1;
x_57 = x_11 + x_56;
x_11 = x_57;
x_12 = x_55;
x_17 = x_54;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
x_59 = l_Lean_instInhabitedExpr;
x_60 = lean_array_get(x_59, x_2, x_49);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_getAppNumArgsAux(x_6, x_61);
lean_inc(x_62);
x_63 = lean_mk_array(x_62, x_1);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_62, x_64);
lean_dec(x_62);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_6, x_63, x_65);
x_67 = l_Lean_mkAppN(x_60, x_66);
x_68 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_69 = l_Array_ofSubarray___rarg(x_68);
x_70 = l_Lean_mkAppN(x_67, x_69);
x_71 = l_Lean_Expr_headBeta(x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_49);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_17);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 4);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_ctor_set_uint8(x_16, 5, x_9);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_23 = lean_whnf(x_1, x_22, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_getAppFn(x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_array_get_size(x_3);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
lean_inc(x_24);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2(x_4, x_5, x_6, x_7, x_8, x_24, x_26, x_27, x_3, x_30, x_31, x_28, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_3);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_reduceMatcher_x3f___lambda__1(x_24, x_36, x_11, x_12, x_13, x_14, x_35);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_32, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = lean_ctor_get_uint8(x_16, 0);
x_49 = lean_ctor_get_uint8(x_16, 1);
x_50 = lean_ctor_get_uint8(x_16, 2);
x_51 = lean_ctor_get_uint8(x_16, 3);
x_52 = lean_ctor_get_uint8(x_16, 4);
x_53 = lean_ctor_get_uint8(x_16, 6);
x_54 = lean_ctor_get_uint8(x_16, 7);
x_55 = lean_ctor_get_uint8(x_16, 8);
x_56 = lean_ctor_get_uint8(x_16, 9);
x_57 = lean_ctor_get_uint8(x_16, 10);
x_58 = lean_ctor_get_uint8(x_16, 11);
x_59 = lean_ctor_get_uint8(x_16, 12);
lean_dec(x_16);
x_60 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_60, 0, x_48);
lean_ctor_set_uint8(x_60, 1, x_49);
lean_ctor_set_uint8(x_60, 2, x_50);
lean_ctor_set_uint8(x_60, 3, x_51);
lean_ctor_set_uint8(x_60, 4, x_52);
lean_ctor_set_uint8(x_60, 5, x_9);
lean_ctor_set_uint8(x_60, 6, x_53);
lean_ctor_set_uint8(x_60, 7, x_54);
lean_ctor_set_uint8(x_60, 8, x_55);
lean_ctor_set_uint8(x_60, 9, x_56);
lean_ctor_set_uint8(x_60, 10, x_57);
lean_ctor_set_uint8(x_60, 11, x_58);
lean_ctor_set_uint8(x_60, 12, x_59);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_17);
lean_ctor_set(x_61, 2, x_18);
lean_ctor_set(x_61, 3, x_19);
lean_ctor_set(x_61, 4, x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_62 = lean_whnf(x_1, x_61, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_getAppFn(x_63);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_2);
x_68 = lean_array_get_size(x_3);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = 0;
lean_inc(x_63);
x_71 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2(x_4, x_5, x_6, x_7, x_8, x_63, x_65, x_66, x_3, x_69, x_70, x_67, x_11, x_12, x_13, x_14, x_64);
lean_dec(x_3);
lean_dec(x_65);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = l_Lean_Meta_reduceMatcher_x3f___lambda__1(x_63, x_75, x_11, x_12, x_13, x_14, x_74);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_63);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_62, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_62, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_83 = x_62;
} else {
 lean_dec_ref(x_62);
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
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_9);
lean_inc(x_8);
x_15 = l_Lean_mkAppN(x_1, x_8);
x_16 = l_Lean_Meta_getTransparency(x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 2;
x_20 = lean_unbox(x_17);
x_21 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_17);
lean_dec(x_17);
x_24 = l_Lean_Meta_reduceMatcher_x3f___lambda__2(x_15, x_2, x_8, x_3, x_4, x_5, x_6, x_7, x_23, x_22, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = 3;
x_26 = lean_box(0);
x_27 = l_Lean_Meta_reduceMatcher_x3f___lambda__2(x_15, x_2, x_8, x_3, x_4, x_5, x_6, x_7, x_25, x_26, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_7);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Meta_reduceMatcher_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_instMonadControlT__1___rarg(x_3);
return x_4;
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
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux(x_1, x_23);
x_25 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_26, x_28);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_nat_add(x_30, x_27);
lean_dec(x_30);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_22);
lean_dec(x_22);
x_36 = lean_nat_add(x_33, x_35);
x_37 = lean_nat_dec_lt(x_34, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_free_object(x_10);
x_38 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_8, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_instantiate_value_lparams(x_39, x_9);
lean_dec(x_9);
lean_dec(x_39);
lean_inc(x_33);
lean_inc(x_29);
x_42 = l_Array_toSubarray___rarg(x_29, x_23, x_33);
x_43 = l_Array_ofSubarray___rarg(x_42);
x_44 = l_Lean_mkAppN(x_41, x_43);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_44);
x_45 = lean_infer_type(x_44, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_ctor_set(x_11, 0, x_35);
x_48 = l_Lean_Meta_reduceMatcher_x3f___closed__1;
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__3), 14, 7);
lean_closure_set(x_49, 0, x_44);
lean_closure_set(x_49, 1, x_33);
lean_closure_set(x_49, 2, x_25);
lean_closure_set(x_49, 3, x_29);
lean_closure_set(x_49, 4, x_34);
lean_closure_set(x_49, 5, x_36);
lean_closure_set(x_49, 6, x_48);
x_50 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_46, x_11, x_49, x_2, x_3, x_4, x_5, x_47);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_free_object(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
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
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
return x_38;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_38);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(3);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_60 = lean_ctor_get(x_11, 0);
lean_inc(x_60);
lean_dec(x_11);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_getAppNumArgsAux(x_1, x_61);
x_63 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_62);
x_64 = lean_mk_array(x_62, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_62, x_65);
lean_dec(x_62);
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_64, x_66);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_nat_add(x_68, x_65);
lean_dec(x_68);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
x_71 = lean_nat_add(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_72 = lean_array_get_size(x_67);
x_73 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_60);
lean_dec(x_60);
x_74 = lean_nat_add(x_71, x_73);
x_75 = lean_nat_dec_lt(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_free_object(x_10);
x_76 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_8, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_instantiate_value_lparams(x_77, x_9);
lean_dec(x_9);
lean_dec(x_77);
lean_inc(x_71);
lean_inc(x_67);
x_80 = l_Array_toSubarray___rarg(x_67, x_61, x_71);
x_81 = l_Array_ofSubarray___rarg(x_80);
x_82 = l_Lean_mkAppN(x_79, x_81);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_82);
x_83 = lean_infer_type(x_82, x_2, x_3, x_4, x_5, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_73);
x_87 = l_Lean_Meta_reduceMatcher_x3f___closed__1;
x_88 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__3), 14, 7);
lean_closure_set(x_88, 0, x_82);
lean_closure_set(x_88, 1, x_71);
lean_closure_set(x_88, 2, x_63);
lean_closure_set(x_88, 3, x_67);
lean_closure_set(x_88, 4, x_72);
lean_closure_set(x_88, 5, x_74);
lean_closure_set(x_88, 6, x_87);
x_89 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_84, x_86, x_88, x_2, x_3, x_4, x_5, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_76, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_96 = x_76;
} else {
 lean_dec_ref(x_76);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_box(3);
lean_ctor_set(x_10, 0, x_98);
return x_10;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_99 = lean_ctor_get(x_10, 1);
lean_inc(x_99);
lean_dec(x_10);
x_100 = lean_ctor_get(x_11, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_101 = x_11;
} else {
 lean_dec_ref(x_11);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Expr_getAppNumArgsAux(x_1, x_102);
x_104 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_103);
x_105 = lean_mk_array(x_103, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_sub(x_103, x_106);
lean_dec(x_103);
x_108 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_105, x_107);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
x_110 = lean_nat_add(x_109, x_106);
lean_dec(x_109);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
x_112 = lean_nat_add(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
x_113 = lean_array_get_size(x_108);
x_114 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_100);
lean_dec(x_100);
x_115 = lean_nat_add(x_112, x_114);
x_116 = lean_nat_dec_lt(x_113, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_8, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_instantiate_value_lparams(x_118, x_9);
lean_dec(x_9);
lean_dec(x_118);
lean_inc(x_112);
lean_inc(x_108);
x_121 = l_Array_toSubarray___rarg(x_108, x_102, x_112);
x_122 = l_Array_ofSubarray___rarg(x_121);
x_123 = l_Lean_mkAppN(x_120, x_122);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_123);
x_124 = lean_infer_type(x_123, x_2, x_3, x_4, x_5, x_119);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
if (lean_is_scalar(x_101)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_101;
}
lean_ctor_set(x_127, 0, x_114);
x_128 = l_Lean_Meta_reduceMatcher_x3f___closed__1;
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__3), 14, 7);
lean_closure_set(x_129, 0, x_123);
lean_closure_set(x_129, 1, x_112);
lean_closure_set(x_129, 2, x_104);
lean_closure_set(x_129, 3, x_108);
lean_closure_set(x_129, 4, x_113);
lean_closure_set(x_129, 5, x_115);
lean_closure_set(x_129, 6, x_128);
x_130 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_125, x_127, x_129, x_2, x_3, x_4, x_5, x_126);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_123);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_117, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_117, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_137 = x_117;
} else {
 lean_dec_ref(x_117);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_box(3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_99);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_box(2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_6);
return x_142;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2___boxed(lean_object** _args) {
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
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18, x_19, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceMatcher_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_Meta_reduceMatcher_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_8);
return x_17;
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Meta_toCtorIfLit(x_10);
x_13 = l_Lean_Expr_getAppFn(x_12);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_environment_find(x_18, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_12);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_22) == 6)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux(x_12, x_24);
x_26 = lean_ctor_get(x_23, 3);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_nat_add(x_26, x_2);
lean_dec(x_26);
x_28 = lean_nat_dec_lt(x_27, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_12);
x_29 = lean_box(0);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Expr_getRevArg_x21(x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_19, 0, x_33);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
}
else
{
lean_object* x_34; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_12);
x_34 = lean_box(0);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
if (lean_obj_tag(x_35) == 6)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Expr_getAppNumArgsAux(x_12, x_37);
x_39 = lean_ctor_get(x_36, 3);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_nat_add(x_39, x_2);
lean_dec(x_39);
x_41 = lean_nat_dec_lt(x_40, x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_12);
x_42 = lean_box(0);
lean_ctor_set(x_15, 0, x_42);
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_nat_sub(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
lean_dec(x_43);
x_46 = l_Lean_Expr_getRevArg_x21(x_12, x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
else
{
lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_12);
x_48 = lean_box(0);
lean_ctor_set(x_15, 0, x_48);
return x_15;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_environment_find(x_51, x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_12);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
if (lean_obj_tag(x_55) == 6)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Expr_getAppNumArgsAux(x_12, x_58);
x_60 = lean_ctor_get(x_57, 3);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_nat_add(x_60, x_2);
lean_dec(x_60);
x_62 = lean_nat_dec_lt(x_61, x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_12);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_nat_sub(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_65, x_66);
lean_dec(x_65);
x_68 = l_Lean_Expr_getRevArg_x21(x_12, x_67);
lean_dec(x_12);
if (lean_is_scalar(x_56)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_56;
}
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_50);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_12);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_73 = lean_box(0);
lean_ctor_set(x_8, 0, x_73);
return x_8;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_76 = l_Lean_Meta_toCtorIfLit(x_74);
x_77 = l_Lean_Expr_getAppFn(x_76);
if (lean_obj_tag(x_77) == 4)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_get(x_6, x_75);
lean_dec(x_6);
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
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_environment_find(x_83, x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
x_85 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_88 = x_84;
} else {
 lean_dec_ref(x_84);
 x_88 = lean_box(0);
}
if (lean_obj_tag(x_87) == 6)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l_Lean_Expr_getAppNumArgsAux(x_76, x_90);
x_92 = lean_ctor_get(x_89, 3);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_nat_add(x_92, x_2);
lean_dec(x_92);
x_94 = lean_nat_dec_lt(x_93, x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_76);
x_95 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_82;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_nat_sub(x_91, x_93);
lean_dec(x_93);
lean_dec(x_91);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_100 = l_Lean_Expr_getRevArg_x21(x_76, x_99);
lean_dec(x_76);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_82)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_82;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_81);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_76);
x_103 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_82;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_81);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_6);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_75);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_12 = l_Lean_Meta_getDelayedAssignment_x3f(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Expr_getAppNumArgsAux(x_2, x_27);
x_29 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_28);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_28, x_31);
lean_dec(x_28);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_30, x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_array_get_size(x_25);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_12);
x_37 = l_Lean_Meta_instantiateMVars(x_26, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Expr_hasExprMVar(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_expr_abstract(x_39, x_25);
lean_dec(x_25);
lean_dec(x_39);
x_42 = lean_expr_instantiate_rev_range(x_41, x_27, x_35, x_33);
lean_dec(x_41);
x_43 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_34, x_33, x_35, x_42);
lean_dec(x_33);
lean_dec(x_34);
lean_ctor_set(x_13, 0, x_43);
lean_ctor_set(x_37, 0, x_13);
return x_37;
}
else
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_25);
lean_free_object(x_13);
x_44 = lean_box(0);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = l_Lean_Expr_hasExprMVar(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_expr_abstract(x_45, x_25);
lean_dec(x_25);
lean_dec(x_45);
x_49 = lean_expr_instantiate_rev_range(x_48, x_27, x_35, x_33);
lean_dec(x_48);
x_50 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_34, x_33, x_35, x_49);
lean_dec(x_33);
lean_dec(x_34);
lean_ctor_set(x_13, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_25);
lean_free_object(x_13);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_25);
lean_free_object(x_13);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_box(0);
lean_ctor_set(x_12, 0, x_58);
return x_12;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Expr_getAppNumArgsAux(x_2, x_63);
x_65 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_64);
x_66 = lean_mk_array(x_64, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_64, x_67);
lean_dec(x_64);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_66, x_68);
x_70 = lean_array_get_size(x_69);
x_71 = lean_array_get_size(x_61);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Meta_instantiateMVars(x_62, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
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
x_77 = l_Lean_Expr_hasExprMVar(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_expr_abstract(x_74, x_61);
lean_dec(x_61);
lean_dec(x_74);
x_79 = lean_expr_instantiate_rev_range(x_78, x_63, x_71, x_69);
lean_dec(x_78);
x_80 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_70, x_69, x_71, x_79);
lean_dec(x_69);
lean_dec(x_70);
lean_ctor_set(x_13, 0, x_80);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_13);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_61);
lean_free_object(x_13);
x_82 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_61);
lean_free_object(x_13);
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_86 = x_73;
} else {
 lean_dec_ref(x_73);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_62);
lean_dec(x_61);
lean_free_object(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_60);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_90 = lean_ctor_get(x_13, 0);
lean_inc(x_90);
lean_dec(x_13);
x_91 = lean_ctor_get(x_12, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_92 = x_12;
} else {
 lean_dec_ref(x_12);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 2);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_Lean_Expr_getAppNumArgsAux(x_2, x_95);
x_97 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_96);
x_98 = lean_mk_array(x_96, x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_sub(x_96, x_99);
lean_dec(x_96);
x_101 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_98, x_100);
x_102 = lean_array_get_size(x_101);
x_103 = lean_array_get_size(x_93);
x_104 = lean_nat_dec_lt(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_92);
x_105 = l_Lean_Meta_instantiateMVars(x_94, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
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
x_109 = l_Lean_Expr_hasExprMVar(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_expr_abstract(x_106, x_93);
lean_dec(x_93);
lean_dec(x_106);
x_111 = lean_expr_instantiate_rev_range(x_110, x_95, x_103, x_101);
lean_dec(x_110);
x_112 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_102, x_101, x_103, x_111);
lean_dec(x_101);
lean_dec(x_102);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_108)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_108;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_107);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_93);
x_115 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_108;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_107);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_93);
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
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
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_92;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_91);
return x_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_levelParams(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthTRAux___rarg(x_3, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_instantiate_value_lparams(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_Expr_betaRev(x_16, x_4);
lean_dec(x_4);
lean_dec(x_16);
x_18 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Meta_whnfCore___spec__4(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.whnfCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__2;
x_2 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1;
x_3 = lean_unsigned_to_nat(385u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Meta_whnfEasyCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_dec(x_2);
switch (lean_obj_tag(x_1)) {
case 4:
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
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_Expr_getAppFn(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_11 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_isLambda(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfDelayedAssigned_x3f(x_12, x_1, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_93; 
x_93 = lean_expr_eqv(x_10, x_12);
lean_dec(x_10);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Lean_Expr_updateFn(x_1, x_12);
x_18 = x_94;
goto block_92;
}
else
{
x_18 = x_1;
goto block_92;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_95 = lean_ctor_get(x_16, 0);
lean_inc(x_95);
lean_dec(x_16);
x_96 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_95, x_3, x_4, x_5, x_6, x_17);
return x_96;
}
block_92:
{
lean_object* x_19; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_18);
x_19 = l_Lean_Meta_reduceMatcher_x3f(x_18, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_22, x_3, x_4, x_5, x_6, x_21);
return x_23;
}
case 2:
{
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
lean_inc(x_18);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2___boxed), 7, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = l_Lean_Meta_getConst_x3f(x_25, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_18);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
switch (lean_obj_tag(x_34)) {
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_27);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = l_Lean_ConstantInfo_name(x_34);
x_37 = l_Lean_Meta_isAuxDef(x_36, x_3, x_4, x_5, x_6, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
lean_ctor_set(x_37, 0, x_18);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Expr_getAppNumArgsAux(x_18, x_45);
x_47 = lean_mk_empty_array_with_capacity(x_46);
lean_dec(x_46);
lean_inc(x_18);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_18, x_47);
x_49 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_18, x_34, x_26, x_48, x_3, x_4, x_5, x_6, x_44);
return x_49;
}
}
case 4:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_dec(x_28);
x_51 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Expr_getAppNumArgsAux(x_18, x_52);
x_54 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_53);
x_55 = lean_mk_array(x_53, x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_53, x_56);
lean_dec(x_53);
x_58 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_18, x_55, x_57);
x_59 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3;
x_60 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_51, x_26, x_58, x_27, x_59, x_3, x_4, x_5, x_6, x_50);
lean_dec(x_58);
lean_dec(x_26);
lean_dec(x_51);
return x_60;
}
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_dec(x_28);
x_62 = lean_ctor_get(x_34, 0);
lean_inc(x_62);
lean_dec(x_34);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Expr_getAppNumArgsAux(x_18, x_63);
x_65 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_64);
x_66 = lean_mk_array(x_64, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_64, x_67);
lean_dec(x_64);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_18, x_66, x_68);
x_70 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3;
x_71 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_62, x_26, x_69, x_27, x_70, x_3, x_4, x_5, x_6, x_61);
return x_71;
}
default: 
{
uint8_t x_72; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_28, 0);
lean_dec(x_73);
lean_ctor_set(x_28, 0, x_18);
return x_28;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_28, 1);
lean_inc(x_74);
lean_dec(x_28);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_18);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_28);
if (x_76 == 0)
{
return x_28;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_28, 0);
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_28);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_19);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_19, 0);
lean_dec(x_81);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_19, 1);
lean_inc(x_82);
lean_dec(x_19);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_18);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
default: 
{
uint8_t x_84; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_19);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_19, 0);
lean_dec(x_85);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_19, 1);
lean_inc(x_86);
lean_dec(x_19);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_18);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_19);
if (x_88 == 0)
{
return x_19;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_19, 0);
x_90 = lean_ctor_get(x_19, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_19);
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
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_15);
if (x_97 == 0)
{
return x_15;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_15, 0);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_15);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_10);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_Expr_getAppNumArgsAux(x_1, x_101);
x_103 = lean_mk_empty_array_with_capacity(x_102);
lean_dec(x_102);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_103);
x_105 = l_Lean_Expr_betaRev(x_12, x_104);
lean_dec(x_104);
lean_dec(x_12);
x_106 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_105, x_3, x_4, x_5, x_6, x_13);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_11);
if (x_107 == 0)
{
return x_11;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_11, 0);
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_11);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
case 8:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_1, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 3);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_expr_instantiate1(x_112, x_111);
lean_dec(x_111);
lean_dec(x_112);
x_114 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_113, x_3, x_4, x_5, x_6, x_7);
return x_114;
}
case 11:
{
lean_object* x_115; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_115 = l_Lean_Meta_reduceProj_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_115, 0);
lean_dec(x_118);
lean_ctor_set(x_115, 0, x_1);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_1);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
lean_dec(x_116);
x_123 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_122, x_3, x_4, x_5, x_6, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_115);
if (x_124 == 0)
{
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_128 = l_Lean_Meta_whnfEasyCases___closed__1;
x_129 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2;
x_130 = lean_panic_fn(x_128, x_129);
x_131 = lean_apply_5(x_130, x_3, x_4, x_5, x_6, x_7);
return x_131;
}
}
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_2 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l_Lean_Meta_whnfEasyCases___closed__1;
x_8 = l_Lean_Meta_whnfEasyCases___closed__5;
x_9 = lean_panic_fn(x_7, x_8);
x_10 = lean_apply_5(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalDecl(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
if (x_20 == 0)
{
lean_object* x_51; 
lean_free_object(x_21);
lean_dec(x_1);
x_51 = lean_box(0);
x_25 = x_51;
goto block_50;
}
else
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_23, 6);
if (x_52 == 0)
{
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_53; 
lean_free_object(x_21);
lean_dec(x_1);
x_53 = lean_box(0);
x_25 = x_53;
goto block_50;
}
}
block_50:
{
uint8_t x_26; 
lean_dec(x_25);
x_26 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_st_ref_get(x_5, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_box(0);
x_36 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_34, x_11, x_35);
lean_ctor_set(x_31, 2, x_36);
x_37 = lean_st_ref_set(x_3, x_31, x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_1 = x_19;
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
x_42 = lean_ctor_get(x_31, 2);
x_43 = lean_ctor_get(x_31, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_44 = lean_box(0);
x_45 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_42, x_11, x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_43);
x_47 = lean_st_ref_set(x_3, x_46, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_1 = x_19;
x_6 = x_48;
goto _start;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_76; 
lean_dec(x_1);
x_76 = lean_box(0);
x_56 = x_76;
goto block_75;
}
else
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_54, 6);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_55);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_1);
x_79 = lean_box(0);
x_56 = x_79;
goto block_75;
}
}
block_75:
{
uint8_t x_57; 
lean_dec(x_56);
x_57 = lean_ctor_get_uint8(x_54, 7);
lean_dec(x_54);
if (x_57 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_55;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_st_ref_get(x_5, x_55);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_3, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
x_70 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_66, x_11, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 4, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_67);
x_72 = lean_st_ref_set(x_3, x_71, x_63);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_1 = x_19;
x_6 = x_73;
goto _start;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = l_Lean_Meta_getExprMVarAssignment_x3f(x_84, x_2, x_3, x_4, x_5, x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
lean_ctor_set(x_85, 0, x_1);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec(x_86);
x_1 = x_92;
x_6 = x_91;
goto _start;
}
}
case 4:
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_94 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_105 = lean_st_ref_get(x_5, x_6);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = 0;
x_95 = x_110;
x_96 = x_109;
goto block_104;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_94, x_2, x_3, x_4, x_5, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_95 = x_115;
x_96 = x_114;
goto block_104;
}
block_104:
{
if (x_95 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_box(0);
x_98 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_97, x_2, x_3, x_4, x_5, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_inc(x_1);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_1);
x_100 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_94, x_99, x_2, x_3, x_4, x_5, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_101, x_2, x_3, x_4, x_5, x_102);
return x_103;
}
}
}
case 5:
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_116 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_127 = lean_st_ref_get(x_5, x_6);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 3);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get_uint8(x_129, sizeof(void*)*1);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_132 = 0;
x_117 = x_132;
x_118 = x_131;
goto block_126;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_dec(x_127);
x_134 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_116, x_2, x_3, x_4, x_5, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_unbox(x_135);
lean_dec(x_135);
x_117 = x_137;
x_118 = x_136;
goto block_126;
}
block_126:
{
if (x_117 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_box(0);
x_120 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_119, x_2, x_3, x_4, x_5, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_inc(x_1);
x_121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_121, 0, x_1);
x_122 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_116, x_121, x_2, x_3, x_4, x_5, x_118);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_123, x_2, x_3, x_4, x_5, x_124);
return x_125;
}
}
}
case 8:
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_138 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_149 = lean_st_ref_get(x_5, x_6);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 3);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_ctor_get_uint8(x_151, sizeof(void*)*1);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = 0;
x_139 = x_154;
x_140 = x_153;
goto block_148;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
lean_dec(x_149);
x_156 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_138, x_2, x_3, x_4, x_5, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unbox(x_157);
lean_dec(x_157);
x_139 = x_159;
x_140 = x_158;
goto block_148;
}
block_148:
{
if (x_139 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
x_142 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_141, x_2, x_3, x_4, x_5, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_inc(x_1);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_1);
x_144 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_138, x_143, x_2, x_3, x_4, x_5, x_140);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_145, x_2, x_3, x_4, x_5, x_146);
return x_147;
}
}
}
case 10:
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
lean_dec(x_1);
x_1 = x_160;
goto _start;
}
case 11:
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_162 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_173 = lean_st_ref_get(x_5, x_6);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 3);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_ctor_get_uint8(x_175, sizeof(void*)*1);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
lean_dec(x_173);
x_178 = 0;
x_163 = x_178;
x_164 = x_177;
goto block_172;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_180 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_162, x_2, x_3, x_4, x_5, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_unbox(x_181);
lean_dec(x_181);
x_163 = x_183;
x_164 = x_182;
goto block_172;
}
block_172:
{
if (x_163 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_box(0);
x_166 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_165, x_2, x_3, x_4, x_5, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_inc(x_1);
x_167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_167, 0, x_1);
x_168 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_162, x_167, x_2, x_3, x_4, x_5, x_164);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3(x_1, x_169, x_2, x_3, x_4, x_5, x_170);
return x_171;
}
}
}
default: 
{
lean_object* x_184; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_1);
lean_ctor_set(x_184, 1, x_6);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = 0;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_1, x_18, x_19, x_20, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_9, 0, x_23);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_9, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_9);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = 0;
x_33 = 1;
x_34 = l_Lean_Meta_mkLambdaFVars(x_1, x_31, x_32, x_33, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
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
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1;
x_20 = lean_array_push(x_19, x_2);
x_21 = 0;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_20, x_18, x_21, x_22, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_23, 0, x_9);
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
lean_ctor_set(x_9, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_9);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_9, 0);
lean_inc(x_33);
lean_dec(x_9);
x_34 = l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1;
x_35 = lean_array_push(x_34, x_2);
x_36 = 0;
x_37 = 1;
x_38 = l_Lean_Meta_mkLambdaFVars(x_35, x_33, x_36, x_37, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__1), 7, 0);
return x_1;
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
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_8, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = l_Lean_mkApp(x_18, x_30);
lean_ctor_set(x_20, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_Lean_mkApp(x_18, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_37 = x_20;
} else {
 lean_dec_ref(x_20);
 x_37 = lean_box(0);
}
x_38 = l_Lean_mkApp(x_18, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
return x_9;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 6:
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1;
x_50 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__1___rarg(x_1, x_49, x_2, x_3, x_4, x_5, x_6);
return x_50;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 3);
lean_inc(x_54);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_53, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2), 7, 1);
lean_closure_set(x_65, 0, x_54);
x_66 = l_Lean_Meta_withLetDecl___at_Lean_Meta_smartUnfoldingReduce_x3f_go___spec__2___rarg(x_51, x_52, x_64, x_65, x_2, x_3, x_4, x_5, x_63);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_55);
if (x_67 == 0)
{
return x_55;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_55, 0);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
case 10:
{
lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_74 = l_Lean_Meta_smartUnfoldingMatch_x3f(x_1);
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_1, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_1, 0);
lean_dec(x_77);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_78; 
lean_inc(x_72);
x_78 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_72, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_free_object(x_1);
lean_dec(x_72);
lean_dec(x_71);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_78, 0, x_82);
return x_78;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_78, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_expr_update_mdata(x_1, x_89);
lean_ctor_set(x_79, 0, x_90);
return x_78;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
lean_dec(x_79);
x_92 = lean_expr_update_mdata(x_1, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_78, 0, x_93);
return x_78;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_dec(x_78);
x_95 = lean_ctor_get(x_79, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_96 = x_79;
} else {
 lean_dec_ref(x_79);
 x_96 = lean_box(0);
}
x_97 = lean_expr_update_mdata(x_1, x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_1);
lean_dec(x_72);
lean_dec(x_71);
x_100 = !lean_is_exclusive(x_78);
if (x_100 == 0)
{
return x_78;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_78, 0);
x_102 = lean_ctor_get(x_78, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_78);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_free_object(x_1);
lean_dec(x_72);
lean_dec(x_71);
x_104 = lean_ctor_get(x_74, 0);
lean_inc(x_104);
lean_dec(x_74);
x_105 = l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(x_104, x_2, x_3, x_4, x_5, x_6);
return x_105;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_106; 
lean_inc(x_72);
x_106 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_72, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_72);
lean_dec(x_71);
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
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_113 = x_106;
} else {
 lean_dec_ref(x_106);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_116, 0, x_71);
lean_ctor_set(x_116, 1, x_72);
lean_ctor_set_uint64(x_116, sizeof(void*)*2, x_73);
x_117 = lean_expr_update_mdata(x_116, x_114);
if (lean_is_scalar(x_115)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_115;
}
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_113)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_113;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_72);
lean_dec(x_71);
x_120 = lean_ctor_get(x_106, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_122 = x_106;
} else {
 lean_dec_ref(x_106);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_72);
lean_dec(x_71);
x_124 = lean_ctor_get(x_74, 0);
lean_inc(x_124);
lean_dec(x_74);
x_125 = l_Lean_Meta_smartUnfoldingReduce_x3f_goMatch(x_124, x_2, x_3, x_4, x_5, x_6);
return x_125;
}
}
}
case 11:
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_1);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_1, 0);
x_128 = lean_ctor_get(x_1, 1);
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
x_130 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_129, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_dec(x_133);
x_134 = lean_box(0);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_130);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_130, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_131);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_expr_update_proj(x_1, x_141);
lean_ctor_set(x_131, 0, x_142);
return x_130;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
lean_dec(x_131);
x_144 = lean_expr_update_proj(x_1, x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_130, 0, x_145);
return x_130;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_130, 1);
lean_inc(x_146);
lean_dec(x_130);
x_147 = lean_ctor_get(x_131, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_148 = x_131;
} else {
 lean_dec_ref(x_131);
 x_148 = lean_box(0);
}
x_149 = lean_expr_update_proj(x_1, x_147);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_152 = !lean_is_exclusive(x_130);
if (x_152 == 0)
{
return x_130;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_130, 0);
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_130);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint64_t x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_1, 0);
x_157 = lean_ctor_get(x_1, 1);
x_158 = lean_ctor_get(x_1, 2);
x_159 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_1);
lean_inc(x_158);
x_160 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_158, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_161, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_170, 0, x_156);
lean_ctor_set(x_170, 1, x_157);
lean_ctor_set(x_170, 2, x_158);
lean_ctor_set_uint64(x_170, sizeof(void*)*3, x_159);
x_171 = lean_expr_update_proj(x_170, x_168);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
if (lean_is_scalar(x_167)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_167;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_166);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_174 = lean_ctor_get(x_160, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_160, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_176 = x_160;
} else {
 lean_dec_ref(x_160);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
default: 
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_1);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_6);
return x_179;
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
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_Meta_smartUnfoldingMatchAlt_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_19, x_2, x_3, x_4, x_5, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_getStuckMVar_x3f(x_27, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_synth_pending(x_37, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_6 = x_47;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_28, 0);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_28);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_7);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_7, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_7, 0, x_59);
return x_7;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
lean_dec(x_7);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_7);
if (x_63 == 0)
{
return x_7;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_7);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
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
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_projectionFnInfoExt;
x_12 = l_Lean_MapDeclarationExtension_find_x3f___at_Lean_Environment_getProjectionFnInfo_x3f___spec__1(x_11, x_10, x_1);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_projectionFnInfoExt;
x_17 = l_Lean_MapDeclarationExtension_find_x3f___at_Lean_Environment_getProjectionFnInfo_x3f___spec__1(x_16, x_15, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = 3;
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1(x_16, x_2, x_3, x_4, x_5, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*3);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_17, 0, x_29);
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 1;
lean_ctor_set_uint8(x_33, 5, x_40);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_41, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = l_Lean_Expr_getAppFn(x_51);
x_53 = l_Lean_Meta_reduceProj_x3f(x_52, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_51);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_53, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Expr_getAppNumArgsAux(x_51, x_65);
x_67 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_66);
x_68 = lean_mk_array(x_66, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_66, x_69);
lean_dec(x_66);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_51, x_68, x_70);
x_72 = l_Lean_mkAppN(x_64, x_71);
x_73 = l_Lean_Expr_headBeta(x_72);
lean_ctor_set(x_54, 0, x_73);
return x_53;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_54, 0);
lean_inc(x_74);
lean_dec(x_54);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux(x_51, x_75);
x_77 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_51, x_78, x_80);
x_82 = l_Lean_mkAppN(x_74, x_81);
x_83 = l_Lean_Expr_headBeta(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_53, 0, x_84);
return x_53;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_85 = lean_ctor_get(x_53, 1);
lean_inc(x_85);
lean_dec(x_53);
x_86 = lean_ctor_get(x_54, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_87 = x_54;
} else {
 lean_dec_ref(x_54);
 x_87 = lean_box(0);
}
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Expr_getAppNumArgsAux(x_51, x_88);
x_90 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_89);
x_91 = lean_mk_array(x_89, x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_89, x_92);
lean_dec(x_89);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_51, x_91, x_93);
x_95 = l_Lean_mkAppN(x_86, x_94);
x_96 = l_Lean_Expr_headBeta(x_95);
if (lean_is_scalar(x_87)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_87;
}
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_51);
x_99 = !lean_is_exclusive(x_53);
if (x_99 == 0)
{
return x_53;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_53, 0);
x_101 = lean_ctor_get(x_53, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_53);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_42);
if (x_103 == 0)
{
return x_42;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get_uint8(x_33, 0);
x_108 = lean_ctor_get_uint8(x_33, 1);
x_109 = lean_ctor_get_uint8(x_33, 2);
x_110 = lean_ctor_get_uint8(x_33, 3);
x_111 = lean_ctor_get_uint8(x_33, 4);
x_112 = lean_ctor_get_uint8(x_33, 6);
x_113 = lean_ctor_get_uint8(x_33, 7);
x_114 = lean_ctor_get_uint8(x_33, 8);
x_115 = lean_ctor_get_uint8(x_33, 9);
x_116 = lean_ctor_get_uint8(x_33, 10);
x_117 = lean_ctor_get_uint8(x_33, 11);
x_118 = lean_ctor_get_uint8(x_33, 12);
lean_dec(x_33);
x_119 = 1;
x_120 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_120, 0, x_107);
lean_ctor_set_uint8(x_120, 1, x_108);
lean_ctor_set_uint8(x_120, 2, x_109);
lean_ctor_set_uint8(x_120, 3, x_110);
lean_ctor_set_uint8(x_120, 4, x_111);
lean_ctor_set_uint8(x_120, 5, x_119);
lean_ctor_set_uint8(x_120, 6, x_112);
lean_ctor_set_uint8(x_120, 7, x_113);
lean_ctor_set_uint8(x_120, 8, x_114);
lean_ctor_set_uint8(x_120, 9, x_115);
lean_ctor_set_uint8(x_120, 10, x_116);
lean_ctor_set_uint8(x_120, 11, x_117);
lean_ctor_set_uint8(x_120, 12, x_118);
x_121 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_35);
lean_ctor_set(x_121, 2, x_36);
lean_ctor_set(x_121, 3, x_37);
lean_ctor_set(x_121, 4, x_38);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_122 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_121, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_dec(x_122);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
lean_dec(x_123);
x_130 = l_Lean_Expr_getAppFn(x_129);
x_131 = l_Lean_Meta_reduceProj_x3f(x_130, x_2, x_3, x_4, x_5, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_129);
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
x_135 = lean_box(0);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_138 = x_131;
} else {
 lean_dec_ref(x_131);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_132, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
 x_140 = lean_box(0);
}
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Lean_Expr_getAppNumArgsAux(x_129, x_141);
x_143 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_142);
x_144 = lean_mk_array(x_142, x_143);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_sub(x_142, x_145);
lean_dec(x_142);
x_147 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_129, x_144, x_146);
x_148 = l_Lean_mkAppN(x_139, x_147);
x_149 = l_Lean_Expr_headBeta(x_148);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_149);
if (lean_is_scalar(x_138)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_138;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_137);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_129);
x_152 = lean_ctor_get(x_131, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_131, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_154 = x_131;
} else {
 lean_dec_ref(x_131);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_ctor_get(x_122, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_122, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_158 = x_122;
} else {
 lean_dec_ref(x_122);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
}
}
else
{
lean_object* x_160; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_box(0);
lean_ctor_set(x_7, 0, x_160);
return x_7;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_7, 0);
x_162 = lean_ctor_get(x_7, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_7);
x_163 = 3;
x_164 = lean_unbox(x_161);
lean_dec(x_161);
x_165 = l___private_Init_Meta_0__Lean_Meta_beqTransparencyMode____x40_Init_Meta___hyg_6829_(x_164, x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_162);
return x_167;
}
else
{
lean_object* x_168; 
x_168 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_168) == 4)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1(x_169, x_2, x_3, x_4, x_5, x_162);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_ctor_get_uint8(x_176, sizeof(void*)*3);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_179 = x_170;
} else {
 lean_dec_ref(x_170);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_182 = lean_ctor_get(x_2, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_170, 1);
lean_inc(x_183);
lean_dec(x_170);
x_184 = lean_ctor_get(x_2, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 4);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_182, 0);
x_189 = lean_ctor_get_uint8(x_182, 1);
x_190 = lean_ctor_get_uint8(x_182, 2);
x_191 = lean_ctor_get_uint8(x_182, 3);
x_192 = lean_ctor_get_uint8(x_182, 4);
x_193 = lean_ctor_get_uint8(x_182, 6);
x_194 = lean_ctor_get_uint8(x_182, 7);
x_195 = lean_ctor_get_uint8(x_182, 8);
x_196 = lean_ctor_get_uint8(x_182, 9);
x_197 = lean_ctor_get_uint8(x_182, 10);
x_198 = lean_ctor_get_uint8(x_182, 11);
x_199 = lean_ctor_get_uint8(x_182, 12);
if (lean_is_exclusive(x_182)) {
 x_200 = x_182;
} else {
 lean_dec_ref(x_182);
 x_200 = lean_box(0);
}
x_201 = 1;
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 0, 13);
} else {
 x_202 = x_200;
}
lean_ctor_set_uint8(x_202, 0, x_188);
lean_ctor_set_uint8(x_202, 1, x_189);
lean_ctor_set_uint8(x_202, 2, x_190);
lean_ctor_set_uint8(x_202, 3, x_191);
lean_ctor_set_uint8(x_202, 4, x_192);
lean_ctor_set_uint8(x_202, 5, x_201);
lean_ctor_set_uint8(x_202, 6, x_193);
lean_ctor_set_uint8(x_202, 7, x_194);
lean_ctor_set_uint8(x_202, 8, x_195);
lean_ctor_set_uint8(x_202, 9, x_196);
lean_ctor_set_uint8(x_202, 10, x_197);
lean_ctor_set_uint8(x_202, 11, x_198);
lean_ctor_set_uint8(x_202, 12, x_199);
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_184);
lean_ctor_set(x_203, 2, x_185);
lean_ctor_set(x_203, 3, x_186);
lean_ctor_set(x_203, 4, x_187);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_204 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_203, x_3, x_4, x_5, x_183);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
lean_dec(x_204);
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
lean_dec(x_205);
x_212 = l_Lean_Expr_getAppFn(x_211);
x_213 = l_Lean_Meta_reduceProj_x3f(x_212, x_2, x_3, x_4, x_5, x_210);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_211);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = lean_box(0);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_214, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
x_223 = lean_unsigned_to_nat(0u);
x_224 = l_Lean_Expr_getAppNumArgsAux(x_211, x_223);
x_225 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_224);
x_226 = lean_mk_array(x_224, x_225);
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_sub(x_224, x_227);
lean_dec(x_224);
x_229 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_211, x_226, x_228);
x_230 = l_Lean_mkAppN(x_221, x_229);
x_231 = l_Lean_Expr_headBeta(x_230);
if (lean_is_scalar(x_222)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_222;
}
lean_ctor_set(x_232, 0, x_231);
if (lean_is_scalar(x_220)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_220;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_219);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_211);
x_234 = lean_ctor_get(x_213, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_213, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_236 = x_213;
} else {
 lean_dec_ref(x_213);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = lean_ctor_get(x_204, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_204, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_240 = x_204;
} else {
 lean_dec_ref(x_204);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_168);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_162);
return x_243;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_ConstantInfo_levelParams(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_List_lengthTRAux___rarg(x_8, x_9);
lean_dec(x_8);
x_11 = l_List_lengthTRAux___rarg(x_2, x_9);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_instantiate_value_lparams(x_1, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_levelParams(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthTRAux___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthTRAux___rarg(x_2, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_instantiate_value_lparams(x_1, x_2);
x_17 = l_Lean_Expr_betaRev(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_levelParams(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthTRAux___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthTRAux___rarg(x_2, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_instantiate_value_lparams(x_1, x_2);
x_17 = l_Lean_Expr_betaRev(x_16, x_3);
lean_dec(x_16);
x_18 = l_Lean_Meta_smartUnfoldingReduce_x3f_go(x_17, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_34; uint8_t x_35; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_34 = l_Lean_Meta_smartUnfolding;
x_35 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_9, x_34);
lean_dec(x_9);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_14);
lean_free_object(x_10);
x_36 = lean_box(0);
x_15 = x_36;
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Meta_smartUnfoldingSuffix;
lean_inc(x_7);
x_38 = lean_name_mk_string(x_7, x_37);
x_39 = l_Lean_Environment_contains(x_14, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_10);
x_40 = lean_box(0);
x_15 = x_40;
goto block_33;
}
else
{
lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
}
block_33:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = l_Lean_Meta_getConstNoEx_x3f(x_7, x_2, x_3, x_4, x_5, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_24, x_8, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
lean_dec(x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_60; uint8_t x_61; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_60 = l_Lean_Meta_smartUnfolding;
x_61 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_9, x_60);
lean_dec(x_9);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_44);
x_62 = lean_box(0);
x_45 = x_62;
goto block_59;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Meta_smartUnfoldingSuffix;
lean_inc(x_7);
x_64 = lean_name_mk_string(x_7, x_63);
x_65 = l_Lean_Environment_contains(x_44, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_45 = x_66;
goto block_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_43);
return x_68;
}
}
block_59:
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_45);
x_46 = l_Lean_Meta_getConstNoEx_x3f(x_7, x_2, x_3, x_4, x_5, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_52, x_8, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
lean_dec(x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
}
}
case 5:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = l_Lean_Expr_getAppFn(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 4)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_getConst_x3f(x_71, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst(x_1, x_2, x_3, x_4, x_5, x_75);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_73, 1);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
lean_dec(x_74);
x_81 = l_Lean_ConstantInfo_levelParams(x_80);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_List_lengthTRAux___rarg(x_81, x_82);
lean_dec(x_81);
x_84 = l_List_lengthTRAux___rarg(x_72, x_82);
x_85 = lean_nat_dec_eq(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = l_Lean_Meta_smartUnfolding;
x_89 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_ConstantInfo_hasValue(x_80);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_box(0);
lean_ctor_set(x_73, 0, x_91);
return x_73;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_73);
x_92 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_93 = lean_mk_empty_array_with_capacity(x_92);
lean_dec(x_92);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_93);
x_95 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_80, x_72, x_94, x_2, x_3, x_4, x_5, x_78);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_94);
lean_dec(x_72);
lean_dec(x_80);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_73);
x_96 = l_Lean_ConstantInfo_name(x_80);
x_97 = l_Lean_Meta_smartUnfoldingSuffix;
lean_inc(x_96);
x_98 = lean_name_mk_string(x_96, x_97);
x_99 = l_Lean_Meta_getConstNoEx_x3f(x_98, x_2, x_3, x_4, x_5, x_78);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_96, x_2, x_3, x_4, x_5, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_102, 1);
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
x_107 = l_Lean_ConstantInfo_hasValue(x_80);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_box(0);
lean_ctor_set(x_102, 0, x_108);
return x_102;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_free_object(x_102);
x_109 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
x_111 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_110);
x_112 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_80, x_72, x_111, x_2, x_3, x_4, x_5, x_105);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_111);
lean_dec(x_72);
lean_dec(x_80);
return x_112;
}
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_102, 1);
lean_inc(x_113);
lean_dec(x_102);
x_114 = l_Lean_ConstantInfo_hasValue(x_80);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_118 = lean_mk_empty_array_with_capacity(x_117);
lean_dec(x_117);
x_119 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_118);
x_120 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_80, x_72, x_119, x_2, x_3, x_4, x_5, x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_119);
lean_dec(x_72);
lean_dec(x_80);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_103);
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_102);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_102, 0);
lean_dec(x_122);
x_123 = lean_box(0);
lean_ctor_set(x_102, 0, x_123);
return x_102;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_102, 1);
lean_inc(x_124);
lean_dec(x_102);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_100, 0);
lean_inc(x_127);
lean_dec(x_100);
if (lean_obj_tag(x_127) == 1)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_96);
lean_dec(x_80);
x_128 = lean_ctor_get(x_99, 1);
lean_inc(x_128);
lean_dec(x_99);
x_129 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_130 = lean_mk_empty_array_with_capacity(x_129);
lean_dec(x_129);
x_131 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_130);
x_132 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(x_127, x_72, x_131, x_2, x_3, x_4, x_5, x_128);
lean_dec(x_131);
lean_dec(x_72);
lean_dec(x_127);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
x_133 = lean_ctor_get(x_99, 1);
lean_inc(x_133);
lean_dec(x_99);
x_134 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_96, x_2, x_3, x_4, x_5, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_134, 0);
lean_dec(x_138);
x_139 = l_Lean_ConstantInfo_hasValue(x_80);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_box(0);
lean_ctor_set(x_134, 0, x_140);
return x_134;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_134);
x_141 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_142 = lean_mk_empty_array_with_capacity(x_141);
lean_dec(x_141);
x_143 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_142);
x_144 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_80, x_72, x_143, x_2, x_3, x_4, x_5, x_137);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_143);
lean_dec(x_72);
lean_dec(x_80);
return x_144;
}
}
else
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_134, 1);
lean_inc(x_145);
lean_dec(x_134);
x_146 = l_Lean_ConstantInfo_hasValue(x_80);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_150 = lean_mk_empty_array_with_capacity(x_149);
lean_dec(x_149);
x_151 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_150);
x_152 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_80, x_72, x_151, x_2, x_3, x_4, x_5, x_145);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_151);
lean_dec(x_72);
lean_dec(x_80);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_135);
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_134);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_134, 0);
lean_dec(x_154);
x_155 = lean_box(0);
lean_ctor_set(x_134, 0, x_155);
return x_134;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_134, 1);
lean_inc(x_156);
lean_dec(x_134);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_159 = lean_ctor_get(x_73, 1);
lean_inc(x_159);
lean_dec(x_73);
x_160 = lean_ctor_get(x_74, 0);
lean_inc(x_160);
lean_dec(x_74);
x_161 = l_Lean_ConstantInfo_levelParams(x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_List_lengthTRAux___rarg(x_161, x_162);
lean_dec(x_161);
x_164 = l_List_lengthTRAux___rarg(x_72, x_162);
x_165 = lean_nat_dec_eq(x_163, x_164);
lean_dec(x_164);
lean_dec(x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_4, 0);
lean_inc(x_168);
x_169 = l_Lean_Meta_smartUnfolding;
x_170 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_168, x_169);
lean_dec(x_168);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_ConstantInfo_hasValue(x_160);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_159);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = l_Lean_Expr_getAppNumArgsAux(x_1, x_162);
x_175 = lean_mk_empty_array_with_capacity(x_174);
lean_dec(x_174);
x_176 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_175);
x_177 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_160, x_72, x_176, x_2, x_3, x_4, x_5, x_159);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_176);
lean_dec(x_72);
lean_dec(x_160);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = l_Lean_ConstantInfo_name(x_160);
x_179 = l_Lean_Meta_smartUnfoldingSuffix;
lean_inc(x_178);
x_180 = lean_name_mk_string(x_178, x_179);
x_181 = l_Lean_Meta_getConstNoEx_x3f(x_180, x_2, x_3, x_4, x_5, x_159);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_178, x_2, x_3, x_4, x_5, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = l_Lean_ConstantInfo_hasValue(x_160);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_187);
x_191 = l_Lean_Expr_getAppNumArgsAux(x_1, x_162);
x_192 = lean_mk_empty_array_with_capacity(x_191);
lean_dec(x_191);
x_193 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_192);
x_194 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_160, x_72, x_193, x_2, x_3, x_4, x_5, x_186);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_193);
lean_dec(x_72);
lean_dec(x_160);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_184, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_196 = x_184;
} else {
 lean_dec_ref(x_184);
 x_196 = lean_box(0);
}
x_197 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
}
else
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_182, 0);
lean_inc(x_199);
lean_dec(x_182);
if (lean_obj_tag(x_199) == 1)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_178);
lean_dec(x_160);
x_200 = lean_ctor_get(x_181, 1);
lean_inc(x_200);
lean_dec(x_181);
x_201 = l_Lean_Expr_getAppNumArgsAux(x_1, x_162);
x_202 = lean_mk_empty_array_with_capacity(x_201);
lean_dec(x_201);
x_203 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_202);
x_204 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(x_199, x_72, x_203, x_2, x_3, x_4, x_5, x_200);
lean_dec(x_203);
lean_dec(x_72);
lean_dec(x_199);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_199);
x_205 = lean_ctor_get(x_181, 1);
lean_inc(x_205);
lean_dec(x_181);
x_206 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_178, x_2, x_3, x_4, x_5, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_ConstantInfo_hasValue(x_160);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_209;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_209);
x_213 = l_Lean_Expr_getAppNumArgsAux(x_1, x_162);
x_214 = lean_mk_empty_array_with_capacity(x_213);
lean_dec(x_213);
x_215 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_214);
x_216 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_160, x_72, x_215, x_2, x_3, x_4, x_5, x_208);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_215);
lean_dec(x_72);
lean_dec(x_160);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_207);
lean_dec(x_160);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_206, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_218 = x_206;
} else {
 lean_dec_ref(x_206);
 x_218 = lean_box(0);
}
x_219 = lean_box(0);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
}
}
}
}
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_73);
if (x_221 == 0)
{
return x_73;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_73, 0);
x_223 = lean_ctor_get(x_73, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_73);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; 
lean_dec(x_70);
x_225 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst(x_1, x_2, x_3, x_4, x_5, x_6);
return x_225;
}
}
default: 
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_box(0);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_6);
return x_227;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldProjInst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unfold definition");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfoldDefinition___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfoldDefinition___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_indentExpr(x_1);
x_11 = l_Lean_Meta_unfoldDefinition___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_unfoldDefinition___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_19 = l_Lean_Meta_unfoldDefinition_x3f(x_9, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = l_Lean_Meta_whnfHeadPred(x_26, x_1, x_3, x_4, x_5, x_6, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_whnfEasyCases(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = l_Lean_Meta_whnfEasyCases___closed__1;
x_9 = l_Lean_Meta_whnfEasyCases___closed__5;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalDecl(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
lean_dec(x_14);
x_22 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
if (x_21 == 0)
{
lean_object* x_52; 
lean_free_object(x_22);
lean_dec(x_2);
x_52 = lean_box(0);
x_26 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = lean_ctor_get_uint8(x_24, 6);
if (x_53 == 0)
{
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_54; 
lean_free_object(x_22);
lean_dec(x_2);
x_54 = lean_box(0);
x_26 = x_54;
goto block_51;
}
}
block_51:
{
uint8_t x_27; 
lean_dec(x_26);
x_27 = lean_ctor_get_uint8(x_24, 7);
lean_dec(x_24);
if (x_27 == 0)
{
lean_dec(x_12);
x_2 = x_20;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_st_ref_get(x_6, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 2);
x_36 = lean_box(0);
x_37 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_35, x_12, x_36);
lean_ctor_set(x_32, 2, x_37);
x_38 = lean_st_ref_set(x_4, x_32, x_33);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_2 = x_20;
x_7 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
x_43 = lean_ctor_get(x_32, 2);
x_44 = lean_ctor_get(x_32, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_45 = lean_box(0);
x_46 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_43, x_12, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_44);
x_48 = lean_st_ref_set(x_4, x_47, x_33);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_2 = x_20;
x_7 = x_49;
goto _start;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_22, 0);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_22);
if (x_21 == 0)
{
lean_object* x_77; 
lean_dec(x_2);
x_77 = lean_box(0);
x_57 = x_77;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_55, 6);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_79, 1, x_56);
return x_79;
}
else
{
lean_object* x_80; 
lean_dec(x_2);
x_80 = lean_box(0);
x_57 = x_80;
goto block_76;
}
}
block_76:
{
uint8_t x_58; 
lean_dec(x_57);
x_58 = lean_ctor_get_uint8(x_55, 7);
lean_dec(x_55);
if (x_58 == 0)
{
lean_dec(x_12);
x_2 = x_20;
x_7 = x_56;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_st_ref_get(x_6, x_56);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_take(x_4, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 x_69 = x_63;
} else {
 lean_dec_ref(x_63);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_67, x_12, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 4, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_68);
x_73 = lean_st_ref_set(x_4, x_72, x_64);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_2 = x_20;
x_7 = x_74;
goto _start;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_13);
if (x_81 == 0)
{
return x_13;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_13, 0);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_13);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 2:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = l_Lean_Meta_getExprMVarAssignment_x3f(x_85, x_3, x_4, x_5, x_6, x_7);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
lean_ctor_set(x_86, 0, x_2);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
lean_dec(x_87);
x_2 = x_93;
x_7 = x_92;
goto _start;
}
}
case 4:
{
lean_object* x_95; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_95 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = l_Lean_Expr_isAppOf(x_97, x_1);
if (x_99 == 0)
{
lean_object* x_100; 
lean_free_object(x_95);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_97);
x_100 = l_Lean_Meta_unfoldDefinition_x3f(x_97, x_3, x_4, x_5, x_6, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_100, 0);
lean_dec(x_103);
lean_ctor_set(x_100, 0, x_97);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_97);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec(x_100);
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
lean_dec(x_101);
x_2 = x_107;
x_7 = x_106;
goto _start;
}
}
else
{
uint8_t x_109; 
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_100, 0);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_100);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_95;
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_95, 0);
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_95);
x_115 = l_Lean_Expr_isAppOf(x_113, x_1);
if (x_115 == 0)
{
lean_object* x_116; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_113);
x_116 = l_Lean_Meta_unfoldDefinition_x3f(x_113, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
x_2 = x_122;
x_7 = x_121;
goto _start;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_126 = x_116;
} else {
 lean_dec_ref(x_116);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_113);
lean_ctor_set(x_128, 1, x_114);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_95);
if (x_129 == 0)
{
return x_95;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_95, 0);
x_131 = lean_ctor_get(x_95, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_95);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 5:
{
lean_object* x_133; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_ctor_get(x_133, 1);
x_137 = l_Lean_Expr_isAppOf(x_135, x_1);
if (x_137 == 0)
{
lean_object* x_138; 
lean_free_object(x_133);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_135);
x_138 = l_Lean_Meta_unfoldDefinition_x3f(x_135, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_138, 0);
lean_dec(x_141);
lean_ctor_set(x_138, 0, x_135);
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_135);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_2 = x_145;
x_7 = x_144;
goto _start;
}
}
else
{
uint8_t x_147; 
lean_dec(x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_138);
if (x_147 == 0)
{
return x_138;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_138, 0);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_138);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_133;
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_133, 0);
x_152 = lean_ctor_get(x_133, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_133);
x_153 = l_Lean_Expr_isAppOf(x_151, x_1);
if (x_153 == 0)
{
lean_object* x_154; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_151);
x_154 = l_Lean_Meta_unfoldDefinition_x3f(x_151, x_3, x_4, x_5, x_6, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_151);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_dec(x_154);
x_160 = lean_ctor_get(x_155, 0);
lean_inc(x_160);
lean_dec(x_155);
x_2 = x_160;
x_7 = x_159;
goto _start;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_151);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_ctor_get(x_154, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_164 = x_154;
} else {
 lean_dec_ref(x_154);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_151);
lean_ctor_set(x_166, 1, x_152);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = !lean_is_exclusive(x_133);
if (x_167 == 0)
{
return x_133;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_133, 0);
x_169 = lean_ctor_get(x_133, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_133);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
case 8:
{
lean_object* x_171; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ctor_get(x_171, 1);
x_175 = l_Lean_Expr_isAppOf(x_173, x_1);
if (x_175 == 0)
{
lean_object* x_176; 
lean_free_object(x_171);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_173);
x_176 = l_Lean_Meta_unfoldDefinition_x3f(x_173, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_176, 0);
lean_dec(x_179);
lean_ctor_set(x_176, 0, x_173);
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
lean_dec(x_176);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_173);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
lean_dec(x_176);
x_183 = lean_ctor_get(x_177, 0);
lean_inc(x_183);
lean_dec(x_177);
x_2 = x_183;
x_7 = x_182;
goto _start;
}
}
else
{
uint8_t x_185; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = !lean_is_exclusive(x_176);
if (x_185 == 0)
{
return x_176;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_176, 0);
x_187 = lean_ctor_get(x_176, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_176);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_171;
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_171, 0);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_171);
x_191 = l_Lean_Expr_isAppOf(x_189, x_1);
if (x_191 == 0)
{
lean_object* x_192; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_189);
x_192 = l_Lean_Meta_unfoldDefinition_x3f(x_189, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_189);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_189);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
lean_dec(x_193);
x_2 = x_198;
x_7 = x_197;
goto _start;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_189);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_ctor_get(x_192, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_202 = x_192;
} else {
 lean_dec_ref(x_192);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_189);
lean_ctor_set(x_204, 1, x_190);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_205 = !lean_is_exclusive(x_171);
if (x_205 == 0)
{
return x_171;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_171, 0);
x_207 = lean_ctor_get(x_171, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_171);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
case 10:
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_2, 1);
lean_inc(x_209);
lean_dec(x_2);
x_2 = x_209;
goto _start;
}
case 11:
{
lean_object* x_211; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_211 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = l_Lean_Expr_isAppOf(x_213, x_1);
if (x_215 == 0)
{
lean_object* x_216; 
lean_free_object(x_211);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_213);
x_216 = l_Lean_Meta_unfoldDefinition_x3f(x_213, x_3, x_4, x_5, x_6, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_218 = !lean_is_exclusive(x_216);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_216, 0);
lean_dec(x_219);
lean_ctor_set(x_216, 0, x_213);
return x_216;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
lean_dec(x_216);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_213);
x_222 = lean_ctor_get(x_216, 1);
lean_inc(x_222);
lean_dec(x_216);
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
lean_dec(x_217);
x_2 = x_223;
x_7 = x_222;
goto _start;
}
}
else
{
uint8_t x_225; 
lean_dec(x_213);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_216);
if (x_225 == 0)
{
return x_216;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_216, 0);
x_227 = lean_ctor_get(x_216, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_216);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_211;
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_211, 0);
x_230 = lean_ctor_get(x_211, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_211);
x_231 = l_Lean_Expr_isAppOf(x_229, x_1);
if (x_231 == 0)
{
lean_object* x_232; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_229);
x_232 = l_Lean_Meta_unfoldDefinition_x3f(x_229, x_3, x_4, x_5, x_6, x_230);
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
lean_ctor_set(x_236, 0, x_229);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_229);
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_ctor_get(x_233, 0);
lean_inc(x_238);
lean_dec(x_233);
x_2 = x_238;
x_7 = x_237;
goto _start;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_229);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_244; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_229);
lean_ctor_set(x_244, 1, x_230);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = !lean_is_exclusive(x_211);
if (x_245 == 0)
{
return x_211;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_211, 0);
x_247 = lean_ctor_get(x_211, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_211);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
default: 
{
lean_object* x_249; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_7);
return x_249;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed), 6, 0);
return x_1;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_getConst_x3f(x_24, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
switch (lean_obj_tag(x_34)) {
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_ConstantInfo_name(x_34);
x_37 = l_Lean_Meta_isAuxDef(x_36, x_2, x_3, x_4, x_5, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Expr_getAppNumArgsAux(x_1, x_47);
x_49 = lean_mk_empty_array_with_capacity(x_48);
lean_dec(x_48);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_49);
x_51 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_34, x_25, x_50, x_2, x_3, x_4, x_5, x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_34);
return x_51;
}
}
case 4:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_dec(x_26);
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Expr_getAppNumArgsAux(x_1, x_54);
x_56 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_57, x_59);
x_61 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_62 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_63 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_53, x_25, x_60, x_61, x_62, x_2, x_3, x_4, x_5, x_52);
lean_dec(x_60);
lean_dec(x_25);
lean_dec(x_53);
return x_63;
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
lean_dec(x_26);
x_65 = lean_ctor_get(x_34, 0);
lean_inc(x_65);
lean_dec(x_34);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_Expr_getAppNumArgsAux(x_1, x_66);
x_68 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_67);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_67, x_70);
lean_dec(x_67);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_69, x_71);
x_73 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_74 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_75 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_65, x_25, x_72, x_73, x_74, x_2, x_3, x_4, x_5, x_64);
return x_75;
}
default: 
{
uint8_t x_76; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_26);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_26, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_26, 0, x_78);
return x_26;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_dec(x_26);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_26);
if (x_82 == 0)
{
return x_26;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_26, 0);
x_84 = lean_ctor_get(x_26, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_26);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
lean_ctor_set(x_10, 0, x_86);
return x_10;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_10, 1);
lean_inc(x_87);
lean_dec(x_10);
x_88 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_88) == 4)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Meta_getConst_x3f(x_89, x_2, x_3, x_4, x_5, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
switch (lean_obj_tag(x_97)) {
case 1:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_99 = l_Lean_ConstantInfo_name(x_97);
x_100 = l_Lean_Meta_isAuxDef(x_99, x_2, x_3, x_4, x_5, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_97);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_dec(x_100);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Expr_getAppNumArgsAux(x_1, x_108);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
x_111 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_110);
x_112 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_97, x_90, x_111, x_2, x_3, x_4, x_5, x_107);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_111);
lean_dec(x_90);
lean_dec(x_97);
return x_112;
}
}
case 4:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_91, 1);
lean_inc(x_113);
lean_dec(x_91);
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
lean_dec(x_97);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lean_Expr_getAppNumArgsAux(x_1, x_115);
x_117 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_116);
x_118 = lean_mk_array(x_116, x_117);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_116, x_119);
lean_dec(x_116);
x_121 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_118, x_120);
x_122 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_123 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_124 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_114, x_90, x_121, x_122, x_123, x_2, x_3, x_4, x_5, x_113);
lean_dec(x_121);
lean_dec(x_90);
lean_dec(x_114);
return x_124;
}
case 7:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_91, 1);
lean_inc(x_125);
lean_dec(x_91);
x_126 = lean_ctor_get(x_97, 0);
lean_inc(x_126);
lean_dec(x_97);
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Lean_Expr_getAppNumArgsAux(x_1, x_127);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1;
lean_inc(x_128);
x_130 = lean_mk_array(x_128, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_128, x_131);
lean_dec(x_128);
x_133 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_130, x_132);
x_134 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_135 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_136 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_126, x_90, x_133, x_134, x_135, x_2, x_3, x_4, x_5, x_125);
return x_136;
}
default: 
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_97);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_ctor_get(x_91, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_138 = x_91;
} else {
 lean_dec_ref(x_91);
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
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_91, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_91, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_143 = x_91;
} else {
 lean_dec_ref(x_91);
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
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_87);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_10);
if (x_147 == 0)
{
return x_10;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_10, 0);
x_149 = lean_ctor_get(x_10, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_10);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = l_Lean_Environment_evalConstCheck___rarg(x_11, x_12, x_1, x_2);
lean_dec(x_12);
x_14 = l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__2;
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_toCtorIfLit___closed__2;
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNative___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBoolNative___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceBoolNative___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_reduceBoolNative___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_reduceBoolNative___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_reduceBoolNative(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_reduceBoolNative___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNatNative___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_reduceNatNative(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBool");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceNat");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__9;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBoolNativeUnsafe___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceNative_x3f___closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNative_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_reduceNative_x3f___closed__4;
x_12 = lean_name_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_reduceNative_x3f___closed__6;
x_14 = lean_name_eq(x_9, x_13);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Meta_reduceNatNativeUnsafe(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_mkNatLit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = l_Lean_mkNatLit(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_9);
x_31 = l_Lean_Meta_reduceBoolNativeUnsafe(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = l_Lean_Meta_reduceNative_x3f___closed__10;
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Meta_reduceNative_x3f___closed__10;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = l_Lean_Meta_reduceNative_x3f___closed__14;
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = l_Lean_Meta_reduceNative_x3f___closed__14;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
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
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 4:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_Meta_toCtorIfLit___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Meta_toCtorIfLit___closed__6;
x_22 = lean_string_dec_eq(x_16, x_21);
lean_dec(x_16);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_8);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_apply_6(x_2, x_24, x_3, x_4, x_5, x_6, x_14);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = l_Lean_Meta_toCtorIfLit___closed__1;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_toCtorIfLit___closed__6;
x_34 = lean_string_dec_eq(x_27, x_33);
lean_dec(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_apply_6(x_2, x_37, x_3, x_4, x_5, x_6, x_26);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_8, 0, x_41);
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_dec(x_8);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_8, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_8, 0, x_47);
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_dec(x_8);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_8);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_8, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_8, 0, x_53);
return x_8;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_dec(x_8);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
case 9:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_9, 0);
lean_inc(x_57);
lean_dec(x_9);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_dec(x_8);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_apply_6(x_2, x_59, x_3, x_4, x_5, x_6, x_58);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_8, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_8, 0, x_63);
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_dec(x_8);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
default: 
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_8, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_8, 0, x_69);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_dec(x_8);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
return x_8;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNatValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNatValue___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 4:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Meta_toCtorIfLit___closed__1;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_toCtorIfLit___closed__6;
x_21 = lean_string_dec_eq(x_15, x_20);
lean_dec(x_15);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_apply_1(x_1, x_23);
x_25 = l_Lean_mkRawNatLit(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = l_Lean_Meta_toCtorIfLit___closed__1;
x_31 = lean_string_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_toCtorIfLit___closed__6;
x_35 = lean_string_dec_eq(x_28, x_34);
lean_dec(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_apply_1(x_1, x_38);
x_40 = l_Lean_mkRawNatLit(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_8, 0, x_45);
return x_8;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_dec(x_8);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_8, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_8, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_8, 0, x_57);
return x_8;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_dec(x_8);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
case 9:
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_9, 0);
lean_inc(x_61);
lean_dec(x_9);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_8, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_apply_1(x_1, x_64);
x_66 = l_Lean_mkRawNatLit(x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_8, 0, x_67);
return x_8;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_8, 1);
lean_inc(x_68);
lean_dec(x_8);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_apply_1(x_1, x_69);
x_71 = l_Lean_mkRawNatLit(x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_61);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_8);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_8, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_8, 0, x_76);
return x_8;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
lean_dec(x_8);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
default: 
{
uint8_t x_80; 
lean_dec(x_9);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_8);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_8, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_8, 0, x_82);
return x_8;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_8, 1);
lean_inc(x_83);
lean_dec(x_8);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_8);
if (x_86 == 0)
{
return x_8;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_8, 0);
x_88 = lean_ctor_get(x_8, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_8);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_8, x_8);
x_10 = l_Lean_mkRawNatLit(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_apply_2(x_1, x_9, x_2);
x_11 = l_Lean_mkRawNatLit(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_apply_2(x_1, x_2, x_9);
x_11 = l_Lean_mkRawNatLit(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_apply_2(x_1, x_2, x_3);
x_11 = l_Lean_mkRawNatLit(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_2 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBinOp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_unfoldDefinition___closed__3;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" op ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__12;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__13;
x_2 = l_Lean_Meta_unfoldDefinition___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 4:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Meta_toCtorIfLit___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_toCtorIfLit___closed__6;
x_23 = lean_string_dec_eq(x_17, x_22);
lean_dec(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; 
lean_free_object(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 4:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_25, 1);
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_string_dec_eq(x_34, x_19);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
uint8_t x_37; 
x_37 = lean_string_dec_eq(x_33, x_22);
lean_dec(x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_25);
x_39 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_50 = lean_st_ref_get(x_7, x_31);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = 0;
x_40 = x_55;
x_41 = x_54;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_39, x_4, x_5, x_6, x_7, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_40 = x_60;
x_41 = x_59;
goto block_49;
}
block_49:
{
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_42, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = l_Lean_Meta_reduceBinNatOp___closed__14;
x_45 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_39, x_44, x_4, x_5, x_6, x_7, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_46, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_48;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_25, 1);
lean_inc(x_61);
lean_dec(x_25);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_dec(x_27);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_string_dec_eq(x_63, x_19);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = lean_string_dec_eq(x_62, x_22);
lean_dec(x_62);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
return x_69;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_70 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_81 = lean_st_ref_get(x_7, x_61);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = 0;
x_71 = x_86;
x_72 = x_85;
goto block_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_70, x_4, x_5, x_6, x_7, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_unbox(x_89);
lean_dec(x_89);
x_71 = x_91;
x_72 = x_90;
goto block_80;
}
block_80:
{
if (x_71 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_box(0);
x_74 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_73, x_4, x_5, x_6, x_7, x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = l_Lean_Meta_reduceBinNatOp___closed__14;
x_76 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_70, x_75, x_4, x_5, x_6, x_7, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_77, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_77);
return x_79;
}
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_25);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_25, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set(x_25, 0, x_94);
return x_25;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_25, 1);
lean_inc(x_95);
lean_dec(x_25);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_25);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_25, 0);
lean_dec(x_99);
x_100 = lean_box(0);
lean_ctor_set(x_25, 0, x_100);
return x_25;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_25, 1);
lean_inc(x_101);
lean_dec(x_25);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_25);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_25, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_25, 0, x_106);
return x_25;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_25, 1);
lean_inc(x_107);
lean_dec(x_25);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
case 9:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_26, 0);
lean_inc(x_110);
lean_dec(x_26);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_111 = lean_ctor_get(x_25, 1);
lean_inc(x_111);
lean_dec(x_25);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_130 = lean_st_ref_get(x_7, x_111);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get_uint8(x_132, sizeof(void*)*1);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_135 = 0;
x_114 = x_135;
x_115 = x_134;
goto block_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_dec(x_130);
x_137 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_113, x_4, x_5, x_6, x_7, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_unbox(x_138);
lean_dec(x_138);
x_114 = x_140;
x_115 = x_139;
goto block_129;
}
block_129:
{
if (x_114 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_box(0);
x_117 = l_Lean_Meta_reduceBinNatOp___lambda__2(x_1, x_112, x_116, x_4, x_5, x_6, x_7, x_115);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_inc(x_112);
x_118 = l_Nat_repr(x_112);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_Meta_reduceBinNatOp___closed__12;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_Meta_unfoldDefinition___closed__3;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_113, x_124, x_4, x_5, x_6, x_7, x_115);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Meta_reduceBinNatOp___lambda__2(x_1, x_112, x_126, x_4, x_5, x_6, x_7, x_127);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_126);
return x_128;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_110);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_25);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_25, 0);
lean_dec(x_142);
x_143 = lean_box(0);
lean_ctor_set(x_25, 0, x_143);
return x_25;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_25, 1);
lean_inc(x_144);
lean_dec(x_25);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
default: 
{
uint8_t x_147; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_25);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_25, 0);
lean_dec(x_148);
x_149 = lean_box(0);
lean_ctor_set(x_25, 0, x_149);
return x_25;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_25, 1);
lean_inc(x_150);
lean_dec(x_25);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_25);
if (x_153 == 0)
{
return x_25;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_25, 0);
x_155 = lean_ctor_get(x_25, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_25);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_9, 1);
lean_inc(x_157);
lean_dec(x_9);
x_158 = lean_ctor_get(x_11, 1);
lean_inc(x_158);
lean_dec(x_11);
x_159 = lean_ctor_get(x_12, 1);
lean_inc(x_159);
lean_dec(x_12);
x_160 = l_Lean_Meta_toCtorIfLit___closed__1;
x_161 = lean_string_dec_eq(x_159, x_160);
lean_dec(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_158);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_157);
return x_163;
}
else
{
lean_object* x_164; uint8_t x_165; 
x_164 = l_Lean_Meta_toCtorIfLit___closed__6;
x_165 = lean_string_dec_eq(x_158, x_164);
lean_dec(x_158);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_157);
return x_167;
}
else
{
lean_object* x_168; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_168 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_157);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
switch (lean_obj_tag(x_169)) {
case 4:
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 1)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_dec(x_170);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_string_dec_eq(x_176, x_160);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_175);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_178 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_173);
return x_179;
}
else
{
uint8_t x_180; 
x_180 = lean_string_dec_eq(x_175, x_164);
lean_dec(x_175);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_181 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_174;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_173);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_174);
x_183 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_194 = lean_st_ref_get(x_7, x_173);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 3);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_ctor_get_uint8(x_196, sizeof(void*)*1);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec(x_194);
x_199 = 0;
x_184 = x_199;
x_185 = x_198;
goto block_193;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
lean_dec(x_194);
x_201 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_183, x_4, x_5, x_6, x_7, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_unbox(x_202);
lean_dec(x_202);
x_184 = x_204;
x_185 = x_203;
goto block_193;
}
block_193:
{
if (x_184 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_box(0);
x_187 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_186, x_4, x_5, x_6, x_7, x_185);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = l_Lean_Meta_reduceBinNatOp___closed__14;
x_189 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_183, x_188, x_4, x_5, x_6, x_7, x_185);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_190, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_190);
return x_192;
}
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_205 = lean_ctor_get(x_168, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_206 = x_168;
} else {
 lean_dec_ref(x_168);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_209 = lean_ctor_get(x_168, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_210 = x_168;
} else {
 lean_dec_ref(x_168);
 x_210 = lean_box(0);
}
x_211 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_213 = lean_ctor_get(x_168, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_214 = x_168;
} else {
 lean_dec_ref(x_168);
 x_214 = lean_box(0);
}
x_215 = lean_box(0);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
}
case 9:
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_169, 0);
lean_inc(x_217);
lean_dec(x_169);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_218 = lean_ctor_get(x_168, 1);
lean_inc(x_218);
lean_dec(x_168);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_237 = lean_st_ref_get(x_7, x_218);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 3);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_ctor_get_uint8(x_239, sizeof(void*)*1);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = 0;
x_221 = x_242;
x_222 = x_241;
goto block_236;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_dec(x_237);
x_244 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_220, x_4, x_5, x_6, x_7, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_221 = x_247;
x_222 = x_246;
goto block_236;
}
block_236:
{
if (x_221 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_box(0);
x_224 = l_Lean_Meta_reduceBinNatOp___lambda__2(x_1, x_219, x_223, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_inc(x_219);
x_225 = l_Nat_repr(x_219);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lean_Meta_reduceBinNatOp___closed__12;
x_229 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l_Lean_Meta_unfoldDefinition___closed__3;
x_231 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_220, x_231, x_4, x_5, x_6, x_7, x_222);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Meta_reduceBinNatOp___lambda__2(x_1, x_219, x_233, x_4, x_5, x_6, x_7, x_234);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_233);
return x_235;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_217);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_248 = lean_ctor_get(x_168, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_249 = x_168;
} else {
 lean_dec_ref(x_168);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
default: 
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_169);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_252 = lean_ctor_get(x_168, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_253 = x_168;
} else {
 lean_dec_ref(x_168);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_256 = lean_ctor_get(x_168, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_168, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_258 = x_168;
} else {
 lean_dec_ref(x_168);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_9);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_9, 0);
lean_dec(x_261);
x_262 = lean_box(0);
lean_ctor_set(x_9, 0, x_262);
return x_9;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_9, 1);
lean_inc(x_263);
lean_dec(x_9);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_9);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_9, 0);
lean_dec(x_267);
x_268 = lean_box(0);
lean_ctor_set(x_9, 0, x_268);
return x_9;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_9, 1);
lean_inc(x_269);
lean_dec(x_9);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_9);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_9, 0);
lean_dec(x_273);
x_274 = lean_box(0);
lean_ctor_set(x_9, 0, x_274);
return x_9;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_9, 1);
lean_inc(x_275);
lean_dec(x_9);
x_276 = lean_box(0);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
case 9:
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_10, 0);
lean_inc(x_278);
lean_dec(x_10);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_9, 1);
lean_inc(x_279);
lean_dec(x_9);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_281 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_279);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
switch (lean_obj_tag(x_282)) {
case 4:
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec(x_282);
if (lean_obj_tag(x_283) == 1)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 1)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_281);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_287 = lean_ctor_get(x_281, 1);
x_288 = lean_ctor_get(x_281, 0);
lean_dec(x_288);
x_289 = lean_ctor_get(x_283, 1);
lean_inc(x_289);
lean_dec(x_283);
x_290 = lean_ctor_get(x_284, 1);
lean_inc(x_290);
lean_dec(x_284);
x_291 = l_Lean_Meta_toCtorIfLit___closed__1;
x_292 = lean_string_dec_eq(x_290, x_291);
lean_dec(x_290);
if (x_292 == 0)
{
lean_object* x_293; 
lean_dec(x_289);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_293 = lean_box(0);
lean_ctor_set(x_281, 0, x_293);
return x_281;
}
else
{
lean_object* x_294; uint8_t x_295; 
x_294 = l_Lean_Meta_toCtorIfLit___closed__6;
x_295 = lean_string_dec_eq(x_289, x_294);
lean_dec(x_289);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_296 = lean_box(0);
lean_ctor_set(x_281, 0, x_296);
return x_281;
}
else
{
lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_free_object(x_281);
x_297 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_317 = lean_st_ref_get(x_7, x_287);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_318, 3);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_ctor_get_uint8(x_319, sizeof(void*)*1);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_317, 1);
lean_inc(x_321);
lean_dec(x_317);
x_322 = 0;
x_298 = x_322;
x_299 = x_321;
goto block_316;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_317, 1);
lean_inc(x_323);
lean_dec(x_317);
x_324 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_297, x_4, x_5, x_6, x_7, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_unbox(x_325);
lean_dec(x_325);
x_298 = x_327;
x_299 = x_326;
goto block_316;
}
block_316:
{
if (x_298 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_box(0);
x_301 = l_Lean_Meta_reduceBinNatOp___lambda__3(x_1, x_280, x_300, x_4, x_5, x_6, x_7, x_299);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_inc(x_280);
x_302 = l_Nat_repr(x_280);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = l_Lean_Meta_unfoldDefinition___closed__3;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
x_307 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_305);
x_312 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_297, x_311, x_4, x_5, x_6, x_7, x_299);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l_Lean_Meta_reduceBinNatOp___lambda__3(x_1, x_280, x_313, x_4, x_5, x_6, x_7, x_314);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_313);
return x_315;
}
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_328 = lean_ctor_get(x_281, 1);
lean_inc(x_328);
lean_dec(x_281);
x_329 = lean_ctor_get(x_283, 1);
lean_inc(x_329);
lean_dec(x_283);
x_330 = lean_ctor_get(x_284, 1);
lean_inc(x_330);
lean_dec(x_284);
x_331 = l_Lean_Meta_toCtorIfLit___closed__1;
x_332 = lean_string_dec_eq(x_330, x_331);
lean_dec(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_329);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_333 = lean_box(0);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_328);
return x_334;
}
else
{
lean_object* x_335; uint8_t x_336; 
x_335 = l_Lean_Meta_toCtorIfLit___closed__6;
x_336 = lean_string_dec_eq(x_329, x_335);
lean_dec(x_329);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_328);
return x_338;
}
else
{
lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_339 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_359 = lean_st_ref_get(x_7, x_328);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_360, 3);
lean_inc(x_361);
lean_dec(x_360);
x_362 = lean_ctor_get_uint8(x_361, sizeof(void*)*1);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; 
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
lean_dec(x_359);
x_364 = 0;
x_340 = x_364;
x_341 = x_363;
goto block_358;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_359, 1);
lean_inc(x_365);
lean_dec(x_359);
x_366 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_339, x_4, x_5, x_6, x_7, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_unbox(x_367);
lean_dec(x_367);
x_340 = x_369;
x_341 = x_368;
goto block_358;
}
block_358:
{
if (x_340 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_box(0);
x_343 = l_Lean_Meta_reduceBinNatOp___lambda__3(x_1, x_280, x_342, x_4, x_5, x_6, x_7, x_341);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_inc(x_280);
x_344 = l_Nat_repr(x_280);
x_345 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_347 = l_Lean_Meta_unfoldDefinition___closed__3;
x_348 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_349 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_350 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_352 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_347);
x_354 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_339, x_353, x_4, x_5, x_6, x_7, x_341);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = l_Lean_Meta_reduceBinNatOp___lambda__3(x_1, x_280, x_355, x_4, x_5, x_6, x_7, x_356);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_355);
return x_357;
}
}
}
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_281);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_281, 0);
lean_dec(x_371);
x_372 = lean_box(0);
lean_ctor_set(x_281, 0, x_372);
return x_281;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_281, 1);
lean_inc(x_373);
lean_dec(x_281);
x_374 = lean_box(0);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
else
{
uint8_t x_376; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_281);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_281, 0);
lean_dec(x_377);
x_378 = lean_box(0);
lean_ctor_set(x_281, 0, x_378);
return x_281;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_281, 1);
lean_inc(x_379);
lean_dec(x_281);
x_380 = lean_box(0);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_283);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_281);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_281, 0);
lean_dec(x_383);
x_384 = lean_box(0);
lean_ctor_set(x_281, 0, x_384);
return x_281;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_281, 1);
lean_inc(x_385);
lean_dec(x_281);
x_386 = lean_box(0);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
}
case 9:
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_282, 0);
lean_inc(x_388);
lean_dec(x_282);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_389 = lean_ctor_get(x_281, 1);
lean_inc(x_389);
lean_dec(x_281);
x_390 = lean_ctor_get(x_388, 0);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_413 = lean_st_ref_get(x_7, x_389);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 3);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_ctor_get_uint8(x_415, sizeof(void*)*1);
lean_dec(x_415);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
lean_dec(x_413);
x_418 = 0;
x_392 = x_418;
x_393 = x_417;
goto block_412;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_413, 1);
lean_inc(x_419);
lean_dec(x_413);
x_420 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_391, x_4, x_5, x_6, x_7, x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_unbox(x_421);
lean_dec(x_421);
x_392 = x_423;
x_393 = x_422;
goto block_412;
}
block_412:
{
if (x_392 == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_box(0);
x_395 = l_Lean_Meta_reduceBinNatOp___lambda__4(x_1, x_280, x_390, x_394, x_4, x_5, x_6, x_7, x_393);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_inc(x_280);
x_396 = l_Nat_repr(x_280);
x_397 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_398, 0, x_397);
x_399 = l_Lean_Meta_unfoldDefinition___closed__3;
x_400 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_402 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
lean_inc(x_390);
x_403 = l_Nat_repr(x_390);
x_404 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_404, 0, x_403);
x_405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_399);
x_408 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_391, x_407, x_4, x_5, x_6, x_7, x_393);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = l_Lean_Meta_reduceBinNatOp___lambda__4(x_1, x_280, x_390, x_409, x_4, x_5, x_6, x_7, x_410);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_409);
return x_411;
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_388);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_281);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_281, 0);
lean_dec(x_425);
x_426 = lean_box(0);
lean_ctor_set(x_281, 0, x_426);
return x_281;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_281, 1);
lean_inc(x_427);
lean_dec(x_281);
x_428 = lean_box(0);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
}
default: 
{
uint8_t x_430; 
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_281);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_281, 0);
lean_dec(x_431);
x_432 = lean_box(0);
lean_ctor_set(x_281, 0, x_432);
return x_281;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_281, 1);
lean_inc(x_433);
lean_dec(x_281);
x_434 = lean_box(0);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_436 = !lean_is_exclusive(x_281);
if (x_436 == 0)
{
return x_281;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_281, 0);
x_438 = lean_ctor_get(x_281, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_281);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_278);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_9);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_9, 0);
lean_dec(x_441);
x_442 = lean_box(0);
lean_ctor_set(x_9, 0, x_442);
return x_9;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_9, 1);
lean_inc(x_443);
lean_dec(x_9);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
}
default: 
{
uint8_t x_446; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_446 = !lean_is_exclusive(x_9);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_9, 0);
lean_dec(x_447);
x_448 = lean_box(0);
lean_ctor_set(x_9, 0, x_448);
return x_9;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_9, 1);
lean_inc(x_449);
lean_dec(x_9);
x_450 = lean_box(0);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_9);
if (x_452 == 0)
{
return x_9;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_9, 0);
x_454 = lean_ctor_get(x_9, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_9);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceBinNatOp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_reduceBinNatOp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_reduceBinNatOp___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatOp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_reduceBinNatOp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceBinNatPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 4:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Meta_toCtorIfLit___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_toCtorIfLit___closed__6;
x_23 = lean_string_dec_eq(x_17, x_22);
lean_dec(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; 
lean_free_object(x_9);
x_25 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 4:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_string_dec_eq(x_33, x_19);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
uint8_t x_36; 
x_36 = lean_string_dec_eq(x_32, x_22);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_25, 0, x_37);
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_apply_2(x_1, x_38, x_38);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Meta_reduceNative_x3f___closed__10;
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Meta_reduceNative_x3f___closed__14;
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_string_dec_eq(x_45, x_19);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_string_dec_eq(x_44, x_22);
lean_dec(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_apply_2(x_1, x_52, x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Meta_reduceNative_x3f___closed__10;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Meta_reduceNative_x3f___closed__14;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
}
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_25);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_25, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_25, 0, x_61);
return x_25;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_25, 1);
lean_inc(x_62);
lean_dec(x_25);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_25, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_25, 0, x_67);
return x_25;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_25, 1);
lean_inc(x_68);
lean_dec(x_25);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_27);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_25, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_25, 0, x_73);
return x_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_25, 1);
lean_inc(x_74);
lean_dec(x_25);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
case 9:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
lean_dec(x_26);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_25);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_25, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_apply_2(x_1, x_81, x_80);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_Lean_Meta_reduceNative_x3f___closed__10;
lean_ctor_set(x_25, 0, x_84);
return x_25;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Meta_reduceNative_x3f___closed__14;
lean_ctor_set(x_25, 0, x_85);
return x_25;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
lean_dec(x_25);
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_apply_2(x_1, x_88, x_87);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Meta_reduceNative_x3f___closed__10;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Meta_reduceNative_x3f___closed__14;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_77);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_25);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_25, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_25, 0, x_97);
return x_25;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_25, 1);
lean_inc(x_98);
lean_dec(x_25);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
default: 
{
uint8_t x_101; 
lean_dec(x_26);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_25);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_25, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_25, 0, x_103);
return x_25;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_25, 1);
lean_inc(x_104);
lean_dec(x_25);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_25);
if (x_107 == 0)
{
return x_25;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_25, 0);
x_109 = lean_ctor_get(x_25, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_25);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_9, 1);
lean_inc(x_111);
lean_dec(x_9);
x_112 = lean_ctor_get(x_11, 1);
lean_inc(x_112);
lean_dec(x_11);
x_113 = lean_ctor_get(x_12, 1);
lean_inc(x_113);
lean_dec(x_12);
x_114 = l_Lean_Meta_toCtorIfLit___closed__1;
x_115 = lean_string_dec_eq(x_113, x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_111);
return x_117;
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = l_Lean_Meta_toCtorIfLit___closed__6;
x_119 = lean_string_dec_eq(x_112, x_118);
lean_dec(x_112);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_111);
return x_121;
}
else
{
lean_object* x_122; 
x_122 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_111);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
switch (lean_obj_tag(x_123)) {
case 4:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
if (lean_obj_tag(x_124) == 1)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 1)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_string_dec_eq(x_130, x_114);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_129);
lean_dec(x_1);
x_132 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_127);
return x_133;
}
else
{
uint8_t x_134; 
x_134 = lean_string_dec_eq(x_129, x_118);
lean_dec(x_129);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_135 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_128;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_127);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_apply_2(x_1, x_137, x_137);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = l_Lean_Meta_reduceNative_x3f___closed__10;
if (lean_is_scalar(x_128)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_128;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_127);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Meta_reduceNative_x3f___closed__14;
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_127);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_1);
x_144 = lean_ctor_get(x_122, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_145 = x_122;
} else {
 lean_dec_ref(x_122);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_1);
x_148 = lean_ctor_get(x_122, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_149 = x_122;
} else {
 lean_dec_ref(x_122);
 x_149 = lean_box(0);
}
x_150 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_124);
lean_dec(x_1);
x_152 = lean_ctor_get(x_122, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_153 = x_122;
} else {
 lean_dec_ref(x_122);
 x_153 = lean_box(0);
}
x_154 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
}
case 9:
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_123, 0);
lean_inc(x_156);
lean_dec(x_123);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_122, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_158 = x_122;
} else {
 lean_dec_ref(x_122);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_apply_2(x_1, x_160, x_159);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Meta_reduceNative_x3f___closed__10;
if (lean_is_scalar(x_158)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_158;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_157);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Lean_Meta_reduceNative_x3f___closed__14;
if (lean_is_scalar(x_158)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_158;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_157);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_156);
lean_dec(x_1);
x_167 = lean_ctor_get(x_122, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_168 = x_122;
} else {
 lean_dec_ref(x_122);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
}
default: 
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_123);
lean_dec(x_1);
x_171 = lean_ctor_get(x_122, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_172 = x_122;
} else {
 lean_dec_ref(x_122);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_1);
x_175 = lean_ctor_get(x_122, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_122, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_177 = x_122;
} else {
 lean_dec_ref(x_122);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_9);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_9, 0);
lean_dec(x_180);
x_181 = lean_box(0);
lean_ctor_set(x_9, 0, x_181);
return x_9;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_9, 1);
lean_inc(x_182);
lean_dec(x_9);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_9);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_9, 0);
lean_dec(x_186);
x_187 = lean_box(0);
lean_ctor_set(x_9, 0, x_187);
return x_9;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_9, 1);
lean_inc(x_188);
lean_dec(x_9);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_9);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_9, 0);
lean_dec(x_192);
x_193 = lean_box(0);
lean_ctor_set(x_9, 0, x_193);
return x_9;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_9, 1);
lean_inc(x_194);
lean_dec(x_9);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
case 9:
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_10, 0);
lean_inc(x_197);
lean_dec(x_10);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_9, 1);
lean_inc(x_198);
lean_dec(x_9);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_198);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
switch (lean_obj_tag(x_201)) {
case 4:
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec(x_201);
if (lean_obj_tag(x_202) == 1)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_200);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_200, 0);
lean_dec(x_206);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_dec(x_202);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_dec(x_203);
x_209 = l_Lean_Meta_toCtorIfLit___closed__1;
x_210 = lean_string_dec_eq(x_208, x_209);
lean_dec(x_208);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_207);
lean_dec(x_199);
lean_dec(x_1);
x_211 = lean_box(0);
lean_ctor_set(x_200, 0, x_211);
return x_200;
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Meta_toCtorIfLit___closed__6;
x_213 = lean_string_dec_eq(x_207, x_212);
lean_dec(x_207);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_199);
lean_dec(x_1);
x_214 = lean_box(0);
lean_ctor_set(x_200, 0, x_214);
return x_200;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = lean_unsigned_to_nat(0u);
x_216 = lean_apply_2(x_1, x_199, x_215);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = l_Lean_Meta_reduceNative_x3f___closed__10;
lean_ctor_set(x_200, 0, x_218);
return x_200;
}
else
{
lean_object* x_219; 
x_219 = l_Lean_Meta_reduceNative_x3f___closed__14;
lean_ctor_set(x_200, 0, x_219);
return x_200;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_200, 1);
lean_inc(x_220);
lean_dec(x_200);
x_221 = lean_ctor_get(x_202, 1);
lean_inc(x_221);
lean_dec(x_202);
x_222 = lean_ctor_get(x_203, 1);
lean_inc(x_222);
lean_dec(x_203);
x_223 = l_Lean_Meta_toCtorIfLit___closed__1;
x_224 = lean_string_dec_eq(x_222, x_223);
lean_dec(x_222);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_221);
lean_dec(x_199);
lean_dec(x_1);
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_220);
return x_226;
}
else
{
lean_object* x_227; uint8_t x_228; 
x_227 = l_Lean_Meta_toCtorIfLit___closed__6;
x_228 = lean_string_dec_eq(x_221, x_227);
lean_dec(x_221);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_199);
lean_dec(x_1);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_220);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_unsigned_to_nat(0u);
x_232 = lean_apply_2(x_1, x_199, x_231);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Lean_Meta_reduceNative_x3f___closed__10;
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_220);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = l_Lean_Meta_reduceNative_x3f___closed__14;
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_220);
return x_237;
}
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_200);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_200, 0);
lean_dec(x_239);
x_240 = lean_box(0);
lean_ctor_set(x_200, 0, x_240);
return x_200;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_200, 1);
lean_inc(x_241);
lean_dec(x_200);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_1);
x_244 = !lean_is_exclusive(x_200);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_200, 0);
lean_dec(x_245);
x_246 = lean_box(0);
lean_ctor_set(x_200, 0, x_246);
return x_200;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_200, 1);
lean_inc(x_247);
lean_dec(x_200);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_200);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_200, 0);
lean_dec(x_251);
x_252 = lean_box(0);
lean_ctor_set(x_200, 0, x_252);
return x_200;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_200, 1);
lean_inc(x_253);
lean_dec(x_200);
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
case 9:
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_201, 0);
lean_inc(x_256);
lean_dec(x_201);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_200);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_258 = lean_ctor_get(x_200, 0);
lean_dec(x_258);
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_apply_2(x_1, x_199, x_259);
x_261 = lean_unbox(x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
x_262 = l_Lean_Meta_reduceNative_x3f___closed__10;
lean_ctor_set(x_200, 0, x_262);
return x_200;
}
else
{
lean_object* x_263; 
x_263 = l_Lean_Meta_reduceNative_x3f___closed__14;
lean_ctor_set(x_200, 0, x_263);
return x_200;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_264 = lean_ctor_get(x_200, 1);
lean_inc(x_264);
lean_dec(x_200);
x_265 = lean_ctor_get(x_256, 0);
lean_inc(x_265);
lean_dec(x_256);
x_266 = lean_apply_2(x_1, x_199, x_265);
x_267 = lean_unbox(x_266);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = l_Lean_Meta_reduceNative_x3f___closed__10;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_264);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = l_Lean_Meta_reduceNative_x3f___closed__14;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_256);
lean_dec(x_199);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_200);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_200, 0);
lean_dec(x_273);
x_274 = lean_box(0);
lean_ctor_set(x_200, 0, x_274);
return x_200;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_200, 1);
lean_inc(x_275);
lean_dec(x_200);
x_276 = lean_box(0);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
default: 
{
uint8_t x_278; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_200);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_200, 0);
lean_dec(x_279);
x_280 = lean_box(0);
lean_ctor_set(x_200, 0, x_280);
return x_200;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_200, 1);
lean_inc(x_281);
lean_dec(x_200);
x_282 = lean_box(0);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_199);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_200);
if (x_284 == 0)
{
return x_200;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_200, 0);
x_286 = lean_ctor_get(x_200, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_200);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_288 = !lean_is_exclusive(x_9);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_9, 0);
lean_dec(x_289);
x_290 = lean_box(0);
lean_ctor_set(x_9, 0, x_290);
return x_9;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_9, 1);
lean_inc(x_291);
lean_dec(x_9);
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
default: 
{
uint8_t x_294; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_9);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_9, 0);
lean_dec(x_295);
x_296 = lean_box(0);
lean_ctor_set(x_9, 0, x_296);
return x_9;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_9, 1);
lean_inc(x_297);
lean_dec(x_9);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_9);
if (x_300 == 0)
{
return x_9;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_9, 0);
x_302 = lean_ctor_get(x_9, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_9);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNat_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sub");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mul");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("div");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mod");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("beq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ble");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_toCtorIfLit___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_ble___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__22() {
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
uint8_t x_7; 
x_7 = l_Lean_Expr_hasFVar(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_toCtorIfLit___closed__4;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Meta_reduceNat_x3f___closed__1;
x_17 = l_Lean_Meta_reduceUnaryNatOp(x_16, x_10, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
case 5:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_reduceNat_x3f___closed__3;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_reduceNat_x3f___closed__5;
x_25 = lean_name_eq(x_21, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_reduceNat_x3f___closed__7;
x_27 = lean_name_eq(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_reduceNat_x3f___closed__9;
x_29 = lean_name_eq(x_21, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_reduceNat_x3f___closed__11;
x_31 = lean_name_eq(x_21, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_reduceNat_x3f___closed__13;
x_33 = lean_name_eq(x_21, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_reduceNat_x3f___closed__15;
x_35 = lean_name_eq(x_21, x_34);
lean_dec(x_21);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Meta_reduceNat_x3f___closed__16;
x_39 = l_Lean_Meta_reduceBinNatPred(x_38, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_40 = l_Lean_Meta_reduceNat_x3f___closed__17;
x_41 = l_Lean_Meta_reduceBinNatPred(x_40, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_21);
x_42 = l_Lean_Meta_reduceNat_x3f___closed__18;
x_43 = l_Lean_Meta_reduceBinNatOp(x_42, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_21);
x_44 = l_Lean_Meta_reduceNat_x3f___closed__19;
x_45 = l_Lean_Meta_reduceBinNatOp(x_44, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = l_Lean_Meta_reduceNat_x3f___closed__20;
x_47 = l_Lean_Meta_reduceBinNatOp(x_46, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
x_48 = l_Lean_Meta_reduceNat_x3f___closed__21;
x_49 = l_Lean_Meta_reduceBinNatOp(x_48, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_21);
x_50 = l_Lean_Meta_reduceNat_x3f___closed__22;
x_51 = l_Lean_Meta_reduceBinNatOp(x_50, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
return x_53;
}
}
default: 
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_reduceNat_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasFVar(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasExprMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, 5);
lean_dec(x_10);
x_12 = lean_box(x_11);
switch (lean_obj_tag(x_12)) {
case 2:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
case 3:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
default: 
{
uint8_t x_29; 
lean_dec(x_12);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
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
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.cached?");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
x_3 = lean_unsigned_to_nat(625u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Meta_whnfEasyCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, 5);
lean_dec(x_11);
x_13 = lean_box(x_12);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_st_ref_get(x_6, x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_4, x_16);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_23 = l_Lean_ExprStructEq_instHashableExprStructEq;
x_24 = l_Std_PersistentHashMap_find_x3f___rarg(x_22, x_23, x_21, x_2);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_30 = l_Lean_ExprStructEq_instHashableExprStructEq;
x_31 = l_Std_PersistentHashMap_find_x3f___rarg(x_29, x_30, x_28, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_3);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_st_ref_get(x_6, x_33);
lean_dec(x_6);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_4, x_35);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_42 = l_Lean_ExprStructEq_instHashableExprStructEq;
x_43 = l_Std_PersistentHashMap_find_x3f___rarg(x_41, x_42, x_40, x_2);
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_49 = l_Lean_ExprStructEq_instHashableExprStructEq;
x_50 = l_Std_PersistentHashMap_find_x3f___rarg(x_48, x_49, x_47, x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_2);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = l_Lean_Meta_whnfEasyCases___closed__1;
x_54 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_55 = lean_panic_fn(x_53, x_54);
x_56 = lean_apply_5(x_55, x_3, x_4, x_5, x_6, x_52);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.cache");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
x_3 = lean_unsigned_to_nat(634u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Meta_whnfEasyCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_getConfig(x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, 5);
lean_dec(x_11);
x_13 = lean_box(x_12);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_st_ref_get(x_7, x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_5, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_19, 4);
x_25 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_26 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_27 = l_Std_PersistentHashMap_insert___rarg(x_25, x_26, x_24, x_2, x_3);
lean_ctor_set(x_19, 4, x_27);
x_28 = lean_st_ref_set(x_5, x_18, x_20);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_3);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
x_35 = lean_ctor_get(x_19, 2);
x_36 = lean_ctor_get(x_19, 3);
x_37 = lean_ctor_get(x_19, 5);
x_38 = lean_ctor_get(x_19, 6);
x_39 = lean_ctor_get(x_19, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_40 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_41 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_42 = l_Std_PersistentHashMap_insert___rarg(x_40, x_41, x_39, x_2, x_3);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_37);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_18, 1, x_43);
x_44 = lean_st_ref_set(x_5, x_18, x_20);
lean_dec(x_5);
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
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 2);
x_50 = lean_ctor_get(x_18, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_19, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_19, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_19, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_19, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_58 = x_19;
} else {
 lean_dec_ref(x_19);
 x_58 = lean_box(0);
}
x_59 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_60 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_61 = l_Std_PersistentHashMap_insert___rarg(x_59, x_60, x_57, x_2, x_3);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 7, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_53);
lean_ctor_set(x_62, 3, x_54);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_55);
lean_ctor_set(x_62, 6, x_56);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_49);
lean_ctor_set(x_63, 3, x_50);
x_64 = lean_st_ref_set(x_5, x_63, x_20);
lean_dec(x_5);
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
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
case 1:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_6);
lean_dec(x_4);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_dec(x_10);
x_69 = lean_st_ref_get(x_7, x_68);
lean_dec(x_7);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_take(x_5, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_72, 1);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_73, 3);
x_79 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_80 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_81 = l_Std_PersistentHashMap_insert___rarg(x_79, x_80, x_78, x_2, x_3);
lean_ctor_set(x_73, 3, x_81);
x_82 = lean_st_ref_set(x_5, x_72, x_74);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set(x_82, 0, x_3);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_3);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
x_89 = lean_ctor_get(x_73, 2);
x_90 = lean_ctor_get(x_73, 4);
x_91 = lean_ctor_get(x_73, 5);
x_92 = lean_ctor_get(x_73, 6);
x_93 = lean_ctor_get(x_73, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_93);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_94 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_95 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_96 = l_Std_PersistentHashMap_insert___rarg(x_94, x_95, x_93, x_2, x_3);
x_97 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_89);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_90);
lean_ctor_set(x_97, 5, x_91);
lean_ctor_set(x_97, 6, x_92);
lean_ctor_set(x_72, 1, x_97);
x_98 = lean_st_ref_set(x_5, x_72, x_74);
lean_dec(x_5);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_3);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_102 = lean_ctor_get(x_72, 0);
x_103 = lean_ctor_get(x_72, 2);
x_104 = lean_ctor_get(x_72, 3);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_72);
x_105 = lean_ctor_get(x_73, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_73, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_73, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_73, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_73, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_73, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_73, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 lean_ctor_release(x_73, 6);
 x_112 = x_73;
} else {
 lean_dec_ref(x_73);
 x_112 = lean_box(0);
}
x_113 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_114 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_3);
x_115 = l_Std_PersistentHashMap_insert___rarg(x_113, x_114, x_111, x_2, x_3);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 7, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_106);
lean_ctor_set(x_116, 2, x_107);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_108);
lean_ctor_set(x_116, 5, x_109);
lean_ctor_set(x_116, 6, x_110);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_103);
lean_ctor_set(x_117, 3, x_104);
x_118 = lean_st_ref_set(x_5, x_117, x_74);
lean_dec(x_5);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_3);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
default: 
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_13);
lean_dec(x_2);
x_122 = lean_ctor_get(x_10, 1);
lean_inc(x_122);
lean_dec(x_10);
x_123 = l_Lean_Meta_whnfEasyCases___closed__1;
x_124 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
x_125 = lean_panic_fn(x_123, x_124);
x_126 = lean_apply_5(x_125, x_4, x_5, x_6, x_7, x_122);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_126, 0);
lean_dec(x_128);
lean_ctor_set(x_126, 0, x_3);
return x_126;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_3);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_126);
if (x_131 == 0)
{
return x_126;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_126, 0);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_126);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l_Lean_Meta_whnfEasyCases___closed__1;
x_8 = l_Lean_Meta_whnfEasyCases___closed__5;
x_9 = lean_panic_fn(x_7, x_8);
x_10 = lean_apply_5(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalDecl(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
if (x_20 == 0)
{
lean_object* x_51; 
lean_free_object(x_21);
lean_dec(x_1);
x_51 = lean_box(0);
x_25 = x_51;
goto block_50;
}
else
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_23, 6);
if (x_52 == 0)
{
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_53; 
lean_free_object(x_21);
lean_dec(x_1);
x_53 = lean_box(0);
x_25 = x_53;
goto block_50;
}
}
block_50:
{
uint8_t x_26; 
lean_dec(x_25);
x_26 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_st_ref_get(x_5, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_box(0);
x_36 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_34, x_11, x_35);
lean_ctor_set(x_31, 2, x_36);
x_37 = lean_st_ref_set(x_3, x_31, x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_1 = x_19;
x_6 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
x_42 = lean_ctor_get(x_31, 2);
x_43 = lean_ctor_get(x_31, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_44 = lean_box(0);
x_45 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_42, x_11, x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_43);
x_47 = lean_st_ref_set(x_3, x_46, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_1 = x_19;
x_6 = x_48;
goto _start;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_76; 
lean_dec(x_1);
x_76 = lean_box(0);
x_56 = x_76;
goto block_75;
}
else
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_54, 6);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_55);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_1);
x_79 = lean_box(0);
x_56 = x_79;
goto block_75;
}
}
block_75:
{
uint8_t x_57; 
lean_dec(x_56);
x_57 = lean_ctor_get_uint8(x_54, 7);
lean_dec(x_54);
if (x_57 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_55;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_st_ref_get(x_5, x_55);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_3, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
x_70 = l_Std_RBNode_insert___at_Lean_Meta_whnfCore___spec__3(x_66, x_11, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 4, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_67);
x_72 = lean_st_ref_set(x_3, x_71, x_63);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_1 = x_19;
x_6 = x_73;
goto _start;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = l_Lean_Meta_getExprMVarAssignment_x3f(x_84, x_2, x_3, x_4, x_5, x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
lean_ctor_set(x_85, 0, x_1);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec(x_86);
x_1 = x_92;
x_6 = x_91;
goto _start;
}
}
case 4:
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
lean_inc(x_4);
x_95 = l_Lean_Core_checkMaxHeartbeats(x_94, x_4, x_5, x_6);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint8_t x_182; 
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
x_182 = l_Lean_Expr_hasFVar(x_1);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = l_Lean_Expr_hasExprMVar(x_1);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_184 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_96);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get_uint8(x_185, 5);
lean_dec(x_185);
x_187 = lean_box(x_186);
switch (lean_obj_tag(x_187)) {
case 2:
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = 0;
x_98 = x_189;
x_99 = x_188;
goto block_181;
}
case 3:
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_184, 1);
lean_inc(x_190);
lean_dec(x_184);
x_191 = 0;
x_98 = x_191;
x_99 = x_190;
goto block_181;
}
default: 
{
lean_object* x_192; uint8_t x_193; 
lean_dec(x_187);
x_192 = lean_ctor_get(x_184, 1);
lean_inc(x_192);
lean_dec(x_184);
x_193 = 1;
x_98 = x_193;
x_99 = x_192;
goto block_181;
}
}
}
else
{
uint8_t x_194; 
x_194 = 0;
x_98 = x_194;
x_99 = x_96;
goto block_181;
}
}
else
{
uint8_t x_195; 
x_195 = 0;
x_98 = x_195;
x_99 = x_96;
goto block_181;
}
block_181:
{
lean_object* x_100; lean_object* x_101; 
if (x_98 == 0)
{
lean_object* x_143; 
x_143 = lean_box(0);
x_100 = x_143;
x_101 = x_99;
goto block_142;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_144 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_99);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_145, 5);
lean_dec(x_145);
x_147 = lean_box(x_146);
switch (lean_obj_tag(x_147)) {
case 0:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_st_ref_get(x_5, x_148);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_ref_get(x_3, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_154, 4);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_157 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_158 = l_Std_PersistentHashMap_find_x3f___rarg(x_156, x_157, x_155, x_1);
x_100 = x_158;
x_101 = x_153;
goto block_142;
}
case 1:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_144, 1);
lean_inc(x_159);
lean_dec(x_144);
x_160 = lean_st_ref_get(x_5, x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_st_ref_get(x_3, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_165, 3);
lean_inc(x_166);
lean_dec(x_165);
x_167 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_168 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_169 = l_Std_PersistentHashMap_find_x3f___rarg(x_167, x_168, x_166, x_1);
x_100 = x_169;
x_101 = x_164;
goto block_142;
}
default: 
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_147);
x_170 = lean_ctor_get(x_144, 1);
lean_inc(x_170);
lean_dec(x_144);
x_171 = l_Lean_Meta_whnfEasyCases___closed__1;
x_172 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_173 = lean_panic_fn(x_171, x_172);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_174 = lean_apply_5(x_173, x_2, x_3, x_4, x_5, x_170);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_100 = x_175;
x_101 = x_176;
goto block_142;
}
else
{
uint8_t x_177; 
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_174);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
}
block_142:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_102; 
lean_dec(x_97);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_102 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_105 = l_Lean_Meta_reduceNat_x3f(x_103, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_108 = l_Lean_Meta_reduceNative_x3f(x_103, x_2, x_3, x_4, x_5, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_111 = l_Lean_Meta_unfoldDefinition_x3f(x_103, x_2, x_3, x_4, x_5, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_98, x_1, x_103, x_2, x_3, x_4, x_5, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_103);
lean_dec(x_1);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_whnf(x_116, x_2, x_3, x_4, x_5, x_115);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_111);
if (x_118 == 0)
{
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_103);
x_122 = lean_ctor_get(x_108, 1);
lean_inc(x_122);
lean_dec(x_108);
x_123 = lean_ctor_get(x_109, 0);
lean_inc(x_123);
lean_dec(x_109);
x_124 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_98, x_1, x_123, x_2, x_3, x_4, x_5, x_122);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_108);
if (x_125 == 0)
{
return x_108;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_108, 0);
x_127 = lean_ctor_get(x_108, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_108);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_103);
x_129 = lean_ctor_get(x_105, 1);
lean_inc(x_129);
lean_dec(x_105);
x_130 = lean_ctor_get(x_106, 0);
lean_inc(x_130);
lean_dec(x_106);
x_131 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_98, x_1, x_130, x_2, x_3, x_4, x_5, x_129);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_105);
if (x_132 == 0)
{
return x_105;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_105, 0);
x_134 = lean_ctor_get(x_105, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_105);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_102);
if (x_136 == 0)
{
return x_102;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_102, 0);
x_138 = lean_ctor_get(x_102, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_102);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_100, 0);
lean_inc(x_140);
lean_dec(x_100);
if (lean_is_scalar(x_97)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_97;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_101);
return x_141;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_95);
if (x_196 == 0)
{
return x_95;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_95, 0);
x_198 = lean_ctor_get(x_95, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_95);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
case 5:
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
lean_inc(x_4);
x_201 = l_Lean_Core_checkMaxHeartbeats(x_200, x_4, x_5, x_6);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_288; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_288 = l_Lean_Expr_hasFVar(x_1);
if (x_288 == 0)
{
uint8_t x_289; 
x_289 = l_Lean_Expr_hasExprMVar(x_1);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; 
x_290 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_202);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get_uint8(x_291, 5);
lean_dec(x_291);
x_293 = lean_box(x_292);
switch (lean_obj_tag(x_293)) {
case 2:
{
lean_object* x_294; uint8_t x_295; 
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_dec(x_290);
x_295 = 0;
x_204 = x_295;
x_205 = x_294;
goto block_287;
}
case 3:
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_290, 1);
lean_inc(x_296);
lean_dec(x_290);
x_297 = 0;
x_204 = x_297;
x_205 = x_296;
goto block_287;
}
default: 
{
lean_object* x_298; uint8_t x_299; 
lean_dec(x_293);
x_298 = lean_ctor_get(x_290, 1);
lean_inc(x_298);
lean_dec(x_290);
x_299 = 1;
x_204 = x_299;
x_205 = x_298;
goto block_287;
}
}
}
else
{
uint8_t x_300; 
x_300 = 0;
x_204 = x_300;
x_205 = x_202;
goto block_287;
}
}
else
{
uint8_t x_301; 
x_301 = 0;
x_204 = x_301;
x_205 = x_202;
goto block_287;
}
block_287:
{
lean_object* x_206; lean_object* x_207; 
if (x_204 == 0)
{
lean_object* x_249; 
x_249 = lean_box(0);
x_206 = x_249;
x_207 = x_205;
goto block_248;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; 
x_250 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_205);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_251, 5);
lean_dec(x_251);
x_253 = lean_box(x_252);
switch (lean_obj_tag(x_253)) {
case 0:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
lean_dec(x_250);
x_255 = lean_st_ref_get(x_5, x_254);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_st_ref_get(x_3, x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_260, 4);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_263 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_264 = l_Std_PersistentHashMap_find_x3f___rarg(x_262, x_263, x_261, x_1);
x_206 = x_264;
x_207 = x_259;
goto block_248;
}
case 1:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_265 = lean_ctor_get(x_250, 1);
lean_inc(x_265);
lean_dec(x_250);
x_266 = lean_st_ref_get(x_5, x_265);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_st_ref_get(x_3, x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_271, 3);
lean_inc(x_272);
lean_dec(x_271);
x_273 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_274 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_275 = l_Std_PersistentHashMap_find_x3f___rarg(x_273, x_274, x_272, x_1);
x_206 = x_275;
x_207 = x_270;
goto block_248;
}
default: 
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_253);
x_276 = lean_ctor_get(x_250, 1);
lean_inc(x_276);
lean_dec(x_250);
x_277 = l_Lean_Meta_whnfEasyCases___closed__1;
x_278 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_279 = lean_panic_fn(x_277, x_278);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_280 = lean_apply_5(x_279, x_2, x_3, x_4, x_5, x_276);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_206 = x_281;
x_207 = x_282;
goto block_248;
}
else
{
uint8_t x_283; 
lean_dec(x_203);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_280);
if (x_283 == 0)
{
return x_280;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_280, 0);
x_285 = lean_ctor_get(x_280, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_280);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
}
block_248:
{
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_208; 
lean_dec(x_203);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_208 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_209);
x_211 = l_Lean_Meta_reduceNat_x3f(x_209, x_2, x_3, x_4, x_5, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_209);
x_214 = l_Lean_Meta_reduceNative_x3f(x_209, x_2, x_3, x_4, x_5, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_209);
x_217 = l_Lean_Meta_unfoldDefinition_x3f(x_209, x_2, x_3, x_4, x_5, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_204, x_1, x_209, x_2, x_3, x_4, x_5, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_209);
lean_dec(x_1);
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec(x_218);
x_223 = lean_whnf(x_222, x_2, x_3, x_4, x_5, x_221);
return x_223;
}
}
else
{
uint8_t x_224; 
lean_dec(x_209);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_217);
if (x_224 == 0)
{
return x_217;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_217, 0);
x_226 = lean_ctor_get(x_217, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_217);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_209);
x_228 = lean_ctor_get(x_214, 1);
lean_inc(x_228);
lean_dec(x_214);
x_229 = lean_ctor_get(x_215, 0);
lean_inc(x_229);
lean_dec(x_215);
x_230 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_204, x_1, x_229, x_2, x_3, x_4, x_5, x_228);
return x_230;
}
}
else
{
uint8_t x_231; 
lean_dec(x_209);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_214);
if (x_231 == 0)
{
return x_214;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_214, 0);
x_233 = lean_ctor_get(x_214, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_214);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_209);
x_235 = lean_ctor_get(x_211, 1);
lean_inc(x_235);
lean_dec(x_211);
x_236 = lean_ctor_get(x_212, 0);
lean_inc(x_236);
lean_dec(x_212);
x_237 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_204, x_1, x_236, x_2, x_3, x_4, x_5, x_235);
return x_237;
}
}
else
{
uint8_t x_238; 
lean_dec(x_209);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_211);
if (x_238 == 0)
{
return x_211;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_211, 0);
x_240 = lean_ctor_get(x_211, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_211);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_208);
if (x_242 == 0)
{
return x_208;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_208, 0);
x_244 = lean_ctor_get(x_208, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_208);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_206, 0);
lean_inc(x_246);
lean_dec(x_206);
if (lean_is_scalar(x_203)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_203;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_207);
return x_247;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_201);
if (x_302 == 0)
{
return x_201;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_201, 0);
x_304 = lean_ctor_get(x_201, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_201);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
case 8:
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
lean_inc(x_4);
x_307 = l_Lean_Core_checkMaxHeartbeats(x_306, x_4, x_5, x_6);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; uint8_t x_394; 
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
x_394 = l_Lean_Expr_hasFVar(x_1);
if (x_394 == 0)
{
uint8_t x_395; 
x_395 = l_Lean_Expr_hasExprMVar(x_1);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_396 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_308);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get_uint8(x_397, 5);
lean_dec(x_397);
x_399 = lean_box(x_398);
switch (lean_obj_tag(x_399)) {
case 2:
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_ctor_get(x_396, 1);
lean_inc(x_400);
lean_dec(x_396);
x_401 = 0;
x_310 = x_401;
x_311 = x_400;
goto block_393;
}
case 3:
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_ctor_get(x_396, 1);
lean_inc(x_402);
lean_dec(x_396);
x_403 = 0;
x_310 = x_403;
x_311 = x_402;
goto block_393;
}
default: 
{
lean_object* x_404; uint8_t x_405; 
lean_dec(x_399);
x_404 = lean_ctor_get(x_396, 1);
lean_inc(x_404);
lean_dec(x_396);
x_405 = 1;
x_310 = x_405;
x_311 = x_404;
goto block_393;
}
}
}
else
{
uint8_t x_406; 
x_406 = 0;
x_310 = x_406;
x_311 = x_308;
goto block_393;
}
}
else
{
uint8_t x_407; 
x_407 = 0;
x_310 = x_407;
x_311 = x_308;
goto block_393;
}
block_393:
{
lean_object* x_312; lean_object* x_313; 
if (x_310 == 0)
{
lean_object* x_355; 
x_355 = lean_box(0);
x_312 = x_355;
x_313 = x_311;
goto block_354;
}
else
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; 
x_356 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_311);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get_uint8(x_357, 5);
lean_dec(x_357);
x_359 = lean_box(x_358);
switch (lean_obj_tag(x_359)) {
case 0:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_360 = lean_ctor_get(x_356, 1);
lean_inc(x_360);
lean_dec(x_356);
x_361 = lean_st_ref_get(x_5, x_360);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_st_ref_get(x_3, x_362);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_ctor_get(x_366, 4);
lean_inc(x_367);
lean_dec(x_366);
x_368 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_369 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_370 = l_Std_PersistentHashMap_find_x3f___rarg(x_368, x_369, x_367, x_1);
x_312 = x_370;
x_313 = x_365;
goto block_354;
}
case 1:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_371 = lean_ctor_get(x_356, 1);
lean_inc(x_371);
lean_dec(x_356);
x_372 = lean_st_ref_get(x_5, x_371);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_374 = lean_st_ref_get(x_3, x_373);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_ctor_get(x_377, 3);
lean_inc(x_378);
lean_dec(x_377);
x_379 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_380 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_381 = l_Std_PersistentHashMap_find_x3f___rarg(x_379, x_380, x_378, x_1);
x_312 = x_381;
x_313 = x_376;
goto block_354;
}
default: 
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_359);
x_382 = lean_ctor_get(x_356, 1);
lean_inc(x_382);
lean_dec(x_356);
x_383 = l_Lean_Meta_whnfEasyCases___closed__1;
x_384 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_385 = lean_panic_fn(x_383, x_384);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_386 = lean_apply_5(x_385, x_2, x_3, x_4, x_5, x_382);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_312 = x_387;
x_313 = x_388;
goto block_354;
}
else
{
uint8_t x_389; 
lean_dec(x_309);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_386);
if (x_389 == 0)
{
return x_386;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_386, 0);
x_391 = lean_ctor_get(x_386, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_386);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
}
}
block_354:
{
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_314; 
lean_dec(x_309);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_314 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_315);
x_317 = l_Lean_Meta_reduceNat_x3f(x_315, x_2, x_3, x_4, x_5, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_315);
x_320 = l_Lean_Meta_reduceNative_x3f(x_315, x_2, x_3, x_4, x_5, x_319);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_315);
x_323 = l_Lean_Meta_unfoldDefinition_x3f(x_315, x_2, x_3, x_4, x_5, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_310, x_1, x_315, x_2, x_3, x_4, x_5, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_315);
lean_dec(x_1);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_ctor_get(x_324, 0);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_whnf(x_328, x_2, x_3, x_4, x_5, x_327);
return x_329;
}
}
else
{
uint8_t x_330; 
lean_dec(x_315);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_323);
if (x_330 == 0)
{
return x_323;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_323, 0);
x_332 = lean_ctor_get(x_323, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_323);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_315);
x_334 = lean_ctor_get(x_320, 1);
lean_inc(x_334);
lean_dec(x_320);
x_335 = lean_ctor_get(x_321, 0);
lean_inc(x_335);
lean_dec(x_321);
x_336 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_310, x_1, x_335, x_2, x_3, x_4, x_5, x_334);
return x_336;
}
}
else
{
uint8_t x_337; 
lean_dec(x_315);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_320);
if (x_337 == 0)
{
return x_320;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_320, 0);
x_339 = lean_ctor_get(x_320, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_320);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_315);
x_341 = lean_ctor_get(x_317, 1);
lean_inc(x_341);
lean_dec(x_317);
x_342 = lean_ctor_get(x_318, 0);
lean_inc(x_342);
lean_dec(x_318);
x_343 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_310, x_1, x_342, x_2, x_3, x_4, x_5, x_341);
return x_343;
}
}
else
{
uint8_t x_344; 
lean_dec(x_315);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_317);
if (x_344 == 0)
{
return x_317;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_317, 0);
x_346 = lean_ctor_get(x_317, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_317);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_314);
if (x_348 == 0)
{
return x_314;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_314, 0);
x_350 = lean_ctor_get(x_314, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_314);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = lean_ctor_get(x_312, 0);
lean_inc(x_352);
lean_dec(x_312);
if (lean_is_scalar(x_309)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_309;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_313);
return x_353;
}
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = !lean_is_exclusive(x_307);
if (x_408 == 0)
{
return x_307;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_307, 0);
x_410 = lean_ctor_get(x_307, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_307);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
case 10:
{
lean_object* x_412; 
x_412 = lean_ctor_get(x_1, 1);
lean_inc(x_412);
lean_dec(x_1);
x_1 = x_412;
goto _start;
}
case 11:
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
lean_inc(x_4);
x_415 = l_Lean_Core_checkMaxHeartbeats(x_414, x_4, x_5, x_6);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; uint8_t x_502; 
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
x_502 = l_Lean_Expr_hasFVar(x_1);
if (x_502 == 0)
{
uint8_t x_503; 
x_503 = l_Lean_Expr_hasExprMVar(x_1);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; 
x_504 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_416);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get_uint8(x_505, 5);
lean_dec(x_505);
x_507 = lean_box(x_506);
switch (lean_obj_tag(x_507)) {
case 2:
{
lean_object* x_508; uint8_t x_509; 
x_508 = lean_ctor_get(x_504, 1);
lean_inc(x_508);
lean_dec(x_504);
x_509 = 0;
x_418 = x_509;
x_419 = x_508;
goto block_501;
}
case 3:
{
lean_object* x_510; uint8_t x_511; 
x_510 = lean_ctor_get(x_504, 1);
lean_inc(x_510);
lean_dec(x_504);
x_511 = 0;
x_418 = x_511;
x_419 = x_510;
goto block_501;
}
default: 
{
lean_object* x_512; uint8_t x_513; 
lean_dec(x_507);
x_512 = lean_ctor_get(x_504, 1);
lean_inc(x_512);
lean_dec(x_504);
x_513 = 1;
x_418 = x_513;
x_419 = x_512;
goto block_501;
}
}
}
else
{
uint8_t x_514; 
x_514 = 0;
x_418 = x_514;
x_419 = x_416;
goto block_501;
}
}
else
{
uint8_t x_515; 
x_515 = 0;
x_418 = x_515;
x_419 = x_416;
goto block_501;
}
block_501:
{
lean_object* x_420; lean_object* x_421; 
if (x_418 == 0)
{
lean_object* x_463; 
x_463 = lean_box(0);
x_420 = x_463;
x_421 = x_419;
goto block_462;
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; 
x_464 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_419);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get_uint8(x_465, 5);
lean_dec(x_465);
x_467 = lean_box(x_466);
switch (lean_obj_tag(x_467)) {
case 0:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_468 = lean_ctor_get(x_464, 1);
lean_inc(x_468);
lean_dec(x_464);
x_469 = lean_st_ref_get(x_5, x_468);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_471 = lean_st_ref_get(x_3, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_ctor_get(x_474, 4);
lean_inc(x_475);
lean_dec(x_474);
x_476 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_477 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_478 = l_Std_PersistentHashMap_find_x3f___rarg(x_476, x_477, x_475, x_1);
x_420 = x_478;
x_421 = x_473;
goto block_462;
}
case 1:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_479 = lean_ctor_get(x_464, 1);
lean_inc(x_479);
lean_dec(x_464);
x_480 = lean_st_ref_get(x_5, x_479);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_st_ref_get(x_3, x_481);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = lean_ctor_get(x_485, 3);
lean_inc(x_486);
lean_dec(x_485);
x_487 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_488 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1);
x_489 = l_Std_PersistentHashMap_find_x3f___rarg(x_487, x_488, x_486, x_1);
x_420 = x_489;
x_421 = x_484;
goto block_462;
}
default: 
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_467);
x_490 = lean_ctor_get(x_464, 1);
lean_inc(x_490);
lean_dec(x_464);
x_491 = l_Lean_Meta_whnfEasyCases___closed__1;
x_492 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_493 = lean_panic_fn(x_491, x_492);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_494 = lean_apply_5(x_493, x_2, x_3, x_4, x_5, x_490);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_420 = x_495;
x_421 = x_496;
goto block_462;
}
else
{
uint8_t x_497; 
lean_dec(x_417);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = !lean_is_exclusive(x_494);
if (x_497 == 0)
{
return x_494;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_494, 0);
x_499 = lean_ctor_get(x_494, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_494);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
}
}
block_462:
{
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_422; 
lean_dec(x_417);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_422 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_423);
x_425 = l_Lean_Meta_reduceNat_x3f(x_423, x_2, x_3, x_4, x_5, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_423);
x_428 = l_Lean_Meta_reduceNative_x3f(x_423, x_2, x_3, x_4, x_5, x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_423);
x_431 = l_Lean_Meta_unfoldDefinition_x3f(x_423, x_2, x_3, x_4, x_5, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_418, x_1, x_423, x_2, x_3, x_4, x_5, x_433);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_423);
lean_dec(x_1);
x_435 = lean_ctor_get(x_431, 1);
lean_inc(x_435);
lean_dec(x_431);
x_436 = lean_ctor_get(x_432, 0);
lean_inc(x_436);
lean_dec(x_432);
x_437 = lean_whnf(x_436, x_2, x_3, x_4, x_5, x_435);
return x_437;
}
}
else
{
uint8_t x_438; 
lean_dec(x_423);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_438 = !lean_is_exclusive(x_431);
if (x_438 == 0)
{
return x_431;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_431, 0);
x_440 = lean_ctor_get(x_431, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_431);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_423);
x_442 = lean_ctor_get(x_428, 1);
lean_inc(x_442);
lean_dec(x_428);
x_443 = lean_ctor_get(x_429, 0);
lean_inc(x_443);
lean_dec(x_429);
x_444 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_418, x_1, x_443, x_2, x_3, x_4, x_5, x_442);
return x_444;
}
}
else
{
uint8_t x_445; 
lean_dec(x_423);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = !lean_is_exclusive(x_428);
if (x_445 == 0)
{
return x_428;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_428, 0);
x_447 = lean_ctor_get(x_428, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_428);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_423);
x_449 = lean_ctor_get(x_425, 1);
lean_inc(x_449);
lean_dec(x_425);
x_450 = lean_ctor_get(x_426, 0);
lean_inc(x_450);
lean_dec(x_426);
x_451 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_418, x_1, x_450, x_2, x_3, x_4, x_5, x_449);
return x_451;
}
}
else
{
uint8_t x_452; 
lean_dec(x_423);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_425);
if (x_452 == 0)
{
return x_425;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_425, 0);
x_454 = lean_ctor_get(x_425, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_425);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
else
{
uint8_t x_456; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_422);
if (x_456 == 0)
{
return x_422;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_422, 0);
x_458 = lean_ctor_get(x_422, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_422);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_460 = lean_ctor_get(x_420, 0);
lean_inc(x_460);
lean_dec(x_420);
if (lean_is_scalar(x_417)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_417;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_421);
return x_461;
}
}
}
}
else
{
uint8_t x_516; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_415);
if (x_516 == 0)
{
return x_415;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_415, 0);
x_518 = lean_ctor_get(x_415, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_415);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
default: 
{
lean_object* x_520; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_1);
lean_ctor_set(x_520, 1, x_6);
return x_520;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_10);
x_13 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_6, 6);
x_20 = lean_ctor_get(x_6, 7);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_20);
x_22 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(x_2, x_4, x_5, x_21, x_7, x_8);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Meta_whnfImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_whnfImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_whnfImp___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Meta_whnfImp___lambda__1(x_7, x_1, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_Meta_whnfImp___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_24; 
lean_free_object(x_13);
x_24 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_3, x_4, x_5, x_6, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Environment_getProjectionStructureName_x3f(x_27, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_apply_1(x_2, x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_3, x_4, x_5, x_6, x_26);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_6085_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_ToExpr(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_ProjFns(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Meta_GetConst(lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_WHNF(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GetConst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_smartUnfoldingSuffix___closed__1 = _init_l_Lean_Meta_smartUnfoldingSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix___closed__1);
l_Lean_Meta_smartUnfoldingSuffix = _init_l_Lean_Meta_smartUnfoldingSuffix();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13____closed__5);
l_Lean_Meta_smartUnfolding___closed__1 = _init_l_Lean_Meta_smartUnfolding___closed__1();
lean_mark_persistent(l_Lean_Meta_smartUnfolding___closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_13_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_smartUnfolding = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_smartUnfolding);
lean_dec_ref(res);
l_Lean_Meta_markSmartUnfoldingMatch___closed__1 = _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatch___closed__1);
l_Lean_Meta_markSmartUnfoldingMatch___closed__2 = _init_l_Lean_Meta_markSmartUnfoldingMatch___closed__2();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldingMatch___closed__2);
l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1 = _init_l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__1);
l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2 = _init_l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2();
lean_mark_persistent(l_Lean_Meta_markSmartUnfoldigMatchAlt___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___closed__1);
l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1 = _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1();
lean_mark_persistent(l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__1);
l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2 = _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2();
lean_mark_persistent(l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__2);
l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3 = _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3();
lean_mark_persistent(l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__3);
l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4 = _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4();
lean_mark_persistent(l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__4);
l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5 = _init_l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5();
lean_mark_persistent(l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___closed__5);
l_Lean_Meta_toCtorIfLit___closed__1 = _init_l_Lean_Meta_toCtorIfLit___closed__1();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__1);
l_Lean_Meta_toCtorIfLit___closed__2 = _init_l_Lean_Meta_toCtorIfLit___closed__2();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__2);
l_Lean_Meta_toCtorIfLit___closed__3 = _init_l_Lean_Meta_toCtorIfLit___closed__3();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__3);
l_Lean_Meta_toCtorIfLit___closed__4 = _init_l_Lean_Meta_toCtorIfLit___closed__4();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__4);
l_Lean_Meta_toCtorIfLit___closed__5 = _init_l_Lean_Meta_toCtorIfLit___closed__5();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__5);
l_Lean_Meta_toCtorIfLit___closed__6 = _init_l_Lean_Meta_toCtorIfLit___closed__6();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__6);
l_Lean_Meta_toCtorIfLit___closed__7 = _init_l_Lean_Meta_toCtorIfLit___closed__7();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__7);
l_Lean_Meta_toCtorIfLit___closed__8 = _init_l_Lean_Meta_toCtorIfLit___closed__8();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__8);
l_Lean_Meta_toCtorIfLit___closed__9 = _init_l_Lean_Meta_toCtorIfLit___closed__9();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__9);
l_Lean_Meta_toCtorIfLit___closed__10 = _init_l_Lean_Meta_toCtorIfLit___closed__10();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__10);
l_Lean_Meta_toCtorIfLit___closed__11 = _init_l_Lean_Meta_toCtorIfLit___closed__11();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__11);
l_Lean_Meta_toCtorIfLit___closed__12 = _init_l_Lean_Meta_toCtorIfLit___closed__12();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__12);
l_Lean_Meta_toCtorIfLit___closed__13 = _init_l_Lean_Meta_toCtorIfLit___closed__13();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__13);
l_Lean_Meta_toCtorIfLit___closed__14 = _init_l_Lean_Meta_toCtorIfLit___closed__14();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__14);
l_Lean_Meta_toCtorIfLit___closed__15 = _init_l_Lean_Meta_toCtorIfLit___closed__15();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__15);
l_Lean_Meta_toCtorIfLit___closed__16 = _init_l_Lean_Meta_toCtorIfLit___closed__16();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__16);
l_Lean_Meta_toCtorIfLit___closed__17 = _init_l_Lean_Meta_toCtorIfLit___closed__17();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__17);
l_Lean_Meta_toCtorIfLit___closed__18 = _init_l_Lean_Meta_toCtorIfLit___closed__18();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__18);
l_Lean_Meta_toCtorIfLit___closed__19 = _init_l_Lean_Meta_toCtorIfLit___closed__19();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__19);
l_Lean_Meta_toCtorIfLit___closed__20 = _init_l_Lean_Meta_toCtorIfLit___closed__20();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__20);
l_Lean_Meta_toCtorIfLit___closed__21 = _init_l_Lean_Meta_toCtorIfLit___closed__21();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__21);
l_Lean_Meta_toCtorIfLit___closed__22 = _init_l_Lean_Meta_toCtorIfLit___closed__22();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__22);
l_Lean_Meta_toCtorIfLit___closed__23 = _init_l_Lean_Meta_toCtorIfLit___closed__23();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__23);
l_Lean_Meta_toCtorIfLit___closed__24 = _init_l_Lean_Meta_toCtorIfLit___closed__24();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__24);
l_Lean_Meta_toCtorIfLit___closed__25 = _init_l_Lean_Meta_toCtorIfLit___closed__25();
lean_mark_persistent(l_Lean_Meta_toCtorIfLit___closed__25);
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
l_Lean_Meta_reduceMatcher_x3f___closed__1 = _init_l_Lean_Meta_reduceMatcher_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceMatcher_x3f___closed__1);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__1);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__2);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__3___closed__3);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3);
l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4 = _init_l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4();
lean_mark_persistent(l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4);
l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1 = _init_l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingReduce_x3f_go___lambda__2___closed__1);
l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1 = _init_l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingReduce_x3f_go___closed__1);
l_Lean_Meta_unfoldDefinition___closed__1 = _init_l_Lean_Meta_unfoldDefinition___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__1);
l_Lean_Meta_unfoldDefinition___closed__2 = _init_l_Lean_Meta_unfoldDefinition___closed__2();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__2);
l_Lean_Meta_unfoldDefinition___closed__3 = _init_l_Lean_Meta_unfoldDefinition___closed__3();
lean_mark_persistent(l_Lean_Meta_unfoldDefinition___closed__3);
l_Lean_Meta_reduceRecMatcher_x3f___closed__1 = _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceRecMatcher_x3f___closed__1);
l_Lean_Meta_reduceRecMatcher_x3f___closed__2 = _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceRecMatcher_x3f___closed__2);
l_Lean_Meta_reduceBoolNativeUnsafe___closed__1 = _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceBoolNativeUnsafe___closed__1);
l_Lean_Meta_reduceBoolNativeUnsafe___closed__2 = _init_l_Lean_Meta_reduceBoolNativeUnsafe___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceBoolNativeUnsafe___closed__2);
l_Lean_Meta_reduceBoolNative___rarg___closed__1 = _init_l_Lean_Meta_reduceBoolNative___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceBoolNative___rarg___closed__1);
l_Lean_Meta_reduceBoolNative___rarg___closed__2 = _init_l_Lean_Meta_reduceBoolNative___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceBoolNative___rarg___closed__2);
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
l_Lean_Meta_reduceNative_x3f___closed__10 = _init_l_Lean_Meta_reduceNative_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__10);
l_Lean_Meta_reduceNative_x3f___closed__11 = _init_l_Lean_Meta_reduceNative_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__11);
l_Lean_Meta_reduceNative_x3f___closed__12 = _init_l_Lean_Meta_reduceNative_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__12);
l_Lean_Meta_reduceNative_x3f___closed__13 = _init_l_Lean_Meta_reduceNative_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__13);
l_Lean_Meta_reduceNative_x3f___closed__14 = _init_l_Lean_Meta_reduceNative_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_reduceNative_x3f___closed__14);
l_Lean_Meta_reduceBinNatOp___closed__1 = _init_l_Lean_Meta_reduceBinNatOp___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__1);
l_Lean_Meta_reduceBinNatOp___closed__2 = _init_l_Lean_Meta_reduceBinNatOp___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__2);
l_Lean_Meta_reduceBinNatOp___closed__3 = _init_l_Lean_Meta_reduceBinNatOp___closed__3();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__3);
l_Lean_Meta_reduceBinNatOp___closed__4 = _init_l_Lean_Meta_reduceBinNatOp___closed__4();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__4);
l_Lean_Meta_reduceBinNatOp___closed__5 = _init_l_Lean_Meta_reduceBinNatOp___closed__5();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__5);
l_Lean_Meta_reduceBinNatOp___closed__6 = _init_l_Lean_Meta_reduceBinNatOp___closed__6();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__6);
l_Lean_Meta_reduceBinNatOp___closed__7 = _init_l_Lean_Meta_reduceBinNatOp___closed__7();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__7);
l_Lean_Meta_reduceBinNatOp___closed__8 = _init_l_Lean_Meta_reduceBinNatOp___closed__8();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__8);
l_Lean_Meta_reduceBinNatOp___closed__9 = _init_l_Lean_Meta_reduceBinNatOp___closed__9();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__9);
l_Lean_Meta_reduceBinNatOp___closed__10 = _init_l_Lean_Meta_reduceBinNatOp___closed__10();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__10);
l_Lean_Meta_reduceBinNatOp___closed__11 = _init_l_Lean_Meta_reduceBinNatOp___closed__11();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__11);
l_Lean_Meta_reduceBinNatOp___closed__12 = _init_l_Lean_Meta_reduceBinNatOp___closed__12();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__12);
l_Lean_Meta_reduceBinNatOp___closed__13 = _init_l_Lean_Meta_reduceBinNatOp___closed__13();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__13);
l_Lean_Meta_reduceBinNatOp___closed__14 = _init_l_Lean_Meta_reduceBinNatOp___closed__14();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__14);
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
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2);
l_Lean_Meta_whnfImp___closed__1 = _init_l_Lean_Meta_whnfImp___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfImp___closed__1);
l_Lean_Meta_whnfImp___closed__2 = _init_l_Lean_Meta_whnfImp___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfImp___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_6085_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
