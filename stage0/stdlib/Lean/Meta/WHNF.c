// Lean compiler output
// Module: Lean.Meta.WHNF
// Imports: Init Lean.ToExpr Lean.AuxRecursor Lean.Meta.Basic Lean.Meta.LevelDefEq Lean.Meta.GetConst Lean.Meta.Match.MatcherInfo
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
lean_object* l_Lean_Meta_reduceNative_x3f___closed__1;
extern lean_object* l_Nat_instDivNat___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___boxed(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__7;
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__2(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2(lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__3;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__16;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___closed__2;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__5;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(uint8_t, uint8_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__7;
lean_object* l_Lean_Meta_whnfImp_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__2(lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprChar___lambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1(lean_object*);
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object*);
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__6;
extern lean_object* l_Lean_auxRecExt;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__4(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedException___closed__1;
lean_object* l_Lean_Meta_toCtorIfLit_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__4(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_smartUnfoldingSuffix;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteSubstring___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__1(lean_object*);
lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
extern lean_object* l_instSubNat___closed__1;
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__2(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_withNatValue_match__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__3;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteProd___rarg___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__2(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__10;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_562____closed__2;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_project_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__2(lean_object*);
extern lean_object* l_instMulNat___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__3;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__7;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
lean_object* l_Lean_Meta_smartUnfoldingSuffix___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3(lean_object*);
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding(lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object*);
extern lean_object* l_Lean_instToExprList___rarg___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__2(lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f_match__1(lean_object*);
extern lean_object* l_Lean_instToExprBool___lambda__1___closed__1;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4937_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15_(lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprList___rarg___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
extern lean_object* l_Lean_instToExprBool___lambda__1___closed__2;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__11;
lean_object* l_Lean_Meta_whnfHeadPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1(lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__4(lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1(lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1(lean_object*);
extern lean_object* l_Lean_instQuoteBool___closed__2;
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
lean_object* l_Lean_Meta_toCtorIfLit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__13;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__4;
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1(lean_object*);
extern lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
lean_object* l_Lean_Meta_reduceBinNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f_match__1(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPred_match__1(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__4(lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__8;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_6227____closed__6;
lean_object* l_Lean_Meta_whnfHeadPred_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1(lean_object*);
extern lean_object* l_instAddNat___closed__1;
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__1;
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__2;
lean_object* l_Lean_Meta_toCtorIfLit___closed__6;
lean_object* l_Lean_Meta_withNatValue_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__15;
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
extern lean_object* l_Lean_Expr_isCharLit___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__1;
lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__5;
lean_object* l_Lean_Meta_whnfCore_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding___boxed(lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__4;
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_whnfCore_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__3;
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__9;
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__2;
extern lean_object* l_Nat_instModNat___closed__1;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
uint8_t l_Lean_Meta_smartUnfoldingDefault;
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
lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_smartUnfoldingSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lean_Meta_smartUnfoldingDefault() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("smartUnfolding");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_smartUnfoldingDefault;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("when computing weak head normal form, use auxiliary definition created for functions defined by structural recursion");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
x_3 = l_Lean_Meta_smartUnfoldingDefault;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isAuxDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_auxRecExt;
x_12 = l_Lean_TagDeclarationExtension_isTagged(x_11, x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = l_Lean_noConfusionExt;
x_14 = l_Lean_TagDeclarationExtension_isTagged(x_13, x_10, x_1);
lean_dec(x_10);
x_15 = lean_box(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_auxRecExt;
x_22 = l_Lean_TagDeclarationExtension_isTagged(x_21, x_20, x_1);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_noConfusionExt;
x_24 = l_Lean_TagDeclarationExtension_isTagged(x_23, x_20, x_1);
lean_dec(x_20);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_isAuxDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isAuxDef(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 2);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 3);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_box(x_13);
x_23 = lean_box(x_14);
x_24 = lean_box(x_15);
x_25 = lean_box(x_16);
x_26 = lean_apply_12(x_2, x_20, x_21, x_17, x_18, x_19, x_10, x_11, x_12, x_22, x_23, x_24, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_2);
x_27 = lean_apply_1(x_3, x_1);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_26 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_27, x_29);
x_31 = l_Array_shrink___rarg(x_30, x_2);
x_32 = l_Lean_mkAppN(x_23, x_31);
lean_dec(x_31);
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
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_38, x_40);
x_42 = l_Array_shrink___rarg(x_41, x_2);
x_43 = l_Lean_mkAppN(x_34, x_42);
lean_dec(x_42);
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
x_51 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_50);
x_52 = lean_mk_array(x_50, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_50, x_53);
lean_dec(x_50);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_52, x_54);
x_56 = l_Array_shrink___rarg(x_55, x_2);
x_57 = l_Lean_mkAppN(x_48, x_56);
lean_dec(x_56);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_toCtorIfLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box_uint64(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box_uint64(x_10);
x_13 = lean_apply_2(x_3, x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
lean_object* l_Lean_Meta_toCtorIfLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_toCtorIfLit_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_instToExprChar___lambda__1___closed__1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteSubstring___closed__2;
x_2 = l_Lean_instQuoteProd___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isCharLit___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__1;
x_2 = l_Lean_Meta_toCtorIfLit___closed__5;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__5;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_toCtorIfLit(lean_object* x_1) {
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
x_8 = l_Lean_mkNatLit(x_7);
x_9 = l_Lean_Meta_toCtorIfLit___closed__1;
x_10 = l_Lean_mkApp(x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_Meta_toCtorIfLit___closed__2;
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
x_14 = l_Lean_Meta_toCtorIfLit___closed__6;
x_15 = l_Lean_Meta_toCtorIfLit___closed__7;
x_16 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_14, x_15, x_13);
x_17 = l_Lean_Meta_toCtorIfLit___closed__4;
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
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_76 = l_Lean_Expr_getAppFn(x_13);
x_77 = l_Lean_RecursorVal_getInduct(x_1);
x_78 = l_Lean_Expr_isConstOf(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_box(0);
lean_ctor_set(x_11, 0, x_79);
return x_11;
}
else
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasExprMVar(x_13);
if (x_80 == 0)
{
lean_object* x_81; 
lean_free_object(x_11);
x_81 = lean_box(0);
x_15 = x_81;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_getAppNumArgsAux(x_13, x_82);
x_84 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
lean_inc(x_13);
x_88 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_85, x_87);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_array_get_size(x_88);
x_91 = l_Array_toSubarray___rarg(x_88, x_89, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 2);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_nat_dec_lt(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_free_object(x_11);
x_96 = lean_box(0);
x_15 = x_96;
goto block_75;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_94, x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_free_object(x_11);
x_99 = lean_box(0);
x_15 = x_99;
goto block_75;
}
else
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_101 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_102 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_92, x_100, x_101);
lean_dec(x_92);
if (x_102 == 0)
{
lean_object* x_103; 
lean_free_object(x_11);
x_103 = lean_box(0);
x_15 = x_103;
goto block_75;
}
else
{
lean_object* x_104; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = lean_box(0);
lean_ctor_set(x_11, 0, x_104);
return x_11;
}
}
}
}
}
block_75:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_13);
x_17 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_13, x_16, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_27);
x_28 = l_Lean_Meta_inferType(x_27, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_isExprDefEq(x_13, x_29, x_3, x_4, x_5, x_6, x_30);
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
lean_free_object(x_18);
lean_dec(x_27);
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
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_18);
lean_dec(x_27);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_18);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_28);
if (x_48 == 0)
{
return x_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_18, 0);
lean_inc(x_52);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_53 = l_Lean_Meta_inferType(x_52, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_isExprDefEq(x_13, x_54, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_52);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_52);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_53, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_73 = x_53;
} else {
 lean_dec_ref(x_53);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_105 = lean_ctor_get(x_11, 0);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_11);
x_141 = l_Lean_Expr_getAppFn(x_105);
x_142 = l_Lean_RecursorVal_getInduct(x_1);
x_143 = l_Lean_Expr_isConstOf(x_141, x_142);
lean_dec(x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_106);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasExprMVar(x_105);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_107 = x_147;
goto block_140;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_148 = lean_unsigned_to_nat(0u);
x_149 = l_Lean_Expr_getAppNumArgsAux(x_105, x_148);
x_150 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_149);
x_151 = lean_mk_array(x_149, x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_sub(x_149, x_152);
lean_dec(x_149);
lean_inc(x_105);
x_154 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_105, x_151, x_153);
x_155 = lean_ctor_get(x_1, 2);
lean_inc(x_155);
x_156 = lean_array_get_size(x_154);
x_157 = l_Array_toSubarray___rarg(x_154, x_155, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 2);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_nat_dec_lt(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
x_162 = lean_box(0);
x_107 = x_162;
goto block_140;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_array_get_size(x_158);
x_164 = lean_nat_dec_le(x_160, x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
x_165 = lean_box(0);
x_107 = x_165;
goto block_140;
}
else
{
size_t x_166; size_t x_167; uint8_t x_168; 
x_166 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_167 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_168 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_158, x_166, x_167);
lean_dec(x_158);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_box(0);
x_107 = x_169;
goto block_140;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_106);
return x_171;
}
}
}
}
}
block_140:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_107);
x_108 = lean_ctor_get(x_1, 2);
lean_inc(x_108);
lean_dec(x_1);
lean_inc(x_105);
x_109 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_105, x_108, x_3, x_4, x_5, x_6, x_106);
lean_dec(x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_116);
x_118 = l_Lean_Meta_inferType(x_116, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_Meta_isExprDefEq(x_105, x_119, x_3, x_4, x_5, x_6, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
lean_dec(x_116);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_125 = x_121;
} else {
 lean_dec_ref(x_121);
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
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_117;
}
lean_ctor_set(x_130, 0, x_116);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_117);
lean_dec(x_116);
x_132 = lean_ctor_get(x_121, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
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
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_ctor_get(x_118, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_118, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_138 = x_118;
} else {
 lean_dec_ref(x_118);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_11);
if (x_172 == 0)
{
return x_11;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_11, 0);
x_174 = lean_ctor_get(x_11, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_11);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_8);
if (x_176 == 0)
{
return x_8;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_8, 0);
x_178 = lean_ctor_get(x_8, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_8);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux(x_15, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_31, x_33);
x_35 = l_List_lengthAux___rarg(x_3, x_28);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_List_lengthAux___rarg(x_37, x_28);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_apply_6(x_2, x_40, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
x_50 = lean_ctor_get(x_27, 2);
lean_inc(x_50);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_37, x_3, x_50);
lean_dec(x_37);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 4);
lean_inc(x_53);
x_54 = lean_nat_add(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_nat_add(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
x_57 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_56, x_4, x_28, x_51);
lean_dec(x_56);
x_58 = lean_array_get_size(x_34);
x_59 = lean_ctor_get(x_27, 1);
lean_inc(x_59);
lean_dec(x_27);
x_60 = lean_nat_sub(x_58, x_59);
lean_dec(x_59);
x_61 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_58, x_34, x_60, x_57);
lean_dec(x_34);
lean_dec(x_58);
x_62 = lean_nat_add(x_5, x_32);
x_63 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_6, x_4, x_62, x_61);
x_64 = lean_apply_6(x_7, x_63, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Lean_Meta_whnf(x_16, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_3(x_2, x_10, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_16 = lean_box_uint64(x_15);
x_17 = lean_box_uint64(x_12);
x_18 = lean_box_uint64(x_10);
x_19 = lean_box_uint64(x_8);
x_20 = lean_apply_9(x_2, x_13, x_14, x_16, x_11, x_17, x_9, x_18, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_apply_1(x_3, x_1);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_apply_1(x_3, x_1);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_apply_1(x_3, x_1);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_apply_1(x_3, x_1);
return x_24;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 2:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 3:
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Meta_whnf(x_18, x_6, x_7, x_8, x_9, x_10);
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
x_72 = l_Lean_Meta_whnf(x_71, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 2:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 3:
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getStuckMVar_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 4:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
case 7:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_apply_1(x_4, x_1);
return x_11;
}
}
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getStuckMVar_x3f_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_2(x_2, x_5, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_3, x_9, x_10, x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getStuckMVar_x3f_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_3(x_4, x_1, x_7, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_4(x_5, x_1, x_11, x_12, x_14);
return x_15;
}
case 10:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_3(x_2, x_16, x_17, x_19);
return x_20;
}
case 11:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_4(x_3, x_21, x_22, x_23, x_25);
return x_26;
}
default: 
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_apply_1(x_6, x_1);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getStuckMVar_x3f_match__4___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_RecursorVal_getMajorIdx(x_1);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_whnf(x_15, x_4, x_5, x_6, x_7, x_8);
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
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_43 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_42);
x_44 = lean_mk_array(x_42, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_42, x_45);
lean_dec(x_42);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_44, x_46);
x_48 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_40, x_29, x_47, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_47);
lean_dec(x_29);
lean_dec(x_40);
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
x_53 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_54, x_56);
x_58 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_50, x_29, x_57, x_2, x_3, x_4, x_5, x_49);
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_50);
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
x_70 = l_Lean_Meta_whnf(x_69, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_whnf(x_16, x_4, x_5, x_6, x_7, x_8);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Meta_whnf(x_30, x_4, x_5, x_6, x_7, x_8);
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
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
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
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_4(x_7, x_1, x_15, x_17, x_2);
return x_18;
}
case 1:
{
lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
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
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_21 = lean_box_uint64(x_20);
x_22 = lean_apply_4(x_10, x_1, x_19, x_21, x_2);
return x_22;
}
case 2:
{
lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
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
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_4(x_11, x_1, x_23, x_25, x_2);
return x_26;
}
case 3:
{
lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
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
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_5, x_1, x_27, x_29, x_2);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
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
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_34 = lean_box_uint64(x_33);
x_35 = lean_apply_5(x_12, x_1, x_31, x_32, x_34, x_2);
return x_35;
}
case 5:
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
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
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_39 = lean_box_uint64(x_38);
x_40 = lean_apply_5(x_13, x_1, x_36, x_37, x_39, x_2);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
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
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_45 = lean_box_uint64(x_44);
x_46 = lean_apply_6(x_4, x_1, x_41, x_42, x_43, x_45, x_2);
return x_46;
}
case 7:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_14);
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
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_51 = lean_box_uint64(x_50);
x_52 = lean_apply_6(x_3, x_1, x_47, x_48, x_49, x_51, x_2);
return x_52;
}
case 8:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_14);
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
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 3);
lean_inc(x_56);
x_57 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_58 = lean_box_uint64(x_57);
x_59 = lean_apply_7(x_9, x_1, x_53, x_54, x_55, x_56, x_58, x_2);
return x_59;
}
case 9:
{
lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_14);
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
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_62 = lean_box_uint64(x_61);
x_63 = lean_apply_4(x_6, x_1, x_60, x_62, x_2);
return x_63;
}
case 10:
{
lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_14);
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
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_67 = lean_box_uint64(x_66);
x_68 = lean_apply_4(x_8, x_64, x_65, x_67, x_2);
return x_68;
}
default: 
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; 
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
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_73 = lean_box_uint64(x_72);
x_74 = lean_apply_6(x_14, x_1, x_69, x_70, x_71, x_73, x_2);
return x_74;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg), 14, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.WHNF");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.whnfEasyCases");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
x_3 = lean_unsigned_to_nat(207u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
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
lean_object* x_52; 
lean_free_object(x_22);
lean_dec(x_1);
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
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_54; 
lean_free_object(x_22);
lean_dec(x_1);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 2);
x_36 = lean_box(0);
x_37 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_35, x_12, x_36);
lean_ctor_set(x_32, 2, x_37);
x_38 = lean_st_ref_set(x_4, x_32, x_33);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_1 = x_20;
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
x_46 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_43, x_12, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_44);
x_48 = lean_st_ref_set(x_4, x_47, x_33);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_1 = x_20;
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
lean_dec(x_1);
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
lean_dec(x_2);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_56);
return x_79;
}
else
{
lean_object* x_80; 
lean_dec(x_1);
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
x_1 = x_20;
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
x_71 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_67, x_12, x_70);
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
x_1 = x_20;
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
lean_dec(x_1);
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
x_85 = lean_ctor_get(x_1, 0);
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
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
lean_ctor_set(x_86, 0, x_1);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
lean_dec(x_87);
x_1 = x_93;
x_7 = x_92;
goto _start;
}
}
case 4:
{
lean_object* x_95; 
x_95 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_95;
}
case 5:
{
lean_object* x_96; 
x_96 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_96;
}
case 8:
{
lean_object* x_97; 
x_97 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_97;
}
case 10:
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
lean_dec(x_1);
x_1 = x_98;
goto _start;
}
case 11:
{
lean_object* x_100; 
x_100 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_100;
}
default: 
{
lean_object* x_101; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_7);
return x_101;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idRhs");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux(x_1, x_3);
x_5 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_4);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_6, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_9, x_7);
x_15 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_10, x_9, x_11, x_14);
lean_dec(x_9);
lean_dec(x_10);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_1;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_ConstantInfo_lparams(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_List_lengthAux___rarg(x_5, x_6);
lean_dec(x_5);
x_8 = l_List_lengthAux___rarg(x_2, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_12 = lean_instantiate_value_lparams(x_1, x_2);
x_13 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_12);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_ConstantInfo_lparams(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthAux___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthAux___rarg(x_2, x_7);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_13 = lean_instantiate_value_lparams(x_1, x_2);
x_14 = l_Lean_Expr_betaRev(x_13, x_3);
lean_dec(x_13);
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_14);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_10 < x_9;
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_uget(x_8, x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_expr_eqv(x_6, x_19);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_11);
x_24 = lean_box(0);
lean_inc(x_7);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1(x_7, x_21, x_24, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = x_10 + x_29;
x_10 = x_30;
x_11 = x_28;
x_16 = x_27;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_7);
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_2, x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Expr_getAppNumArgsAux(x_5, x_34);
lean_inc(x_35);
x_36 = lean_mk_array(x_35, x_1);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_35, x_37);
lean_dec(x_35);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_36, x_38);
x_40 = l_Lean_mkAppN(x_33, x_39);
lean_dec(x_39);
x_41 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_42 = l_Array_ofSubarray___rarg(x_41);
lean_dec(x_41);
x_43 = l_Lean_mkAppN(x_40, x_42);
lean_dec(x_42);
x_44 = l_Lean_Expr_headBeta(x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_11, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_16);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_expr_eqv(x_6, x_19);
lean_dec(x_19);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_50 = lean_box(0);
lean_inc(x_7);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1(x_7, x_48, x_50, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = 1;
x_56 = x_10 + x_55;
x_10 = x_56;
x_11 = x_54;
x_16 = x_53;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_7);
x_58 = l_Lean_instInhabitedExpr;
x_59 = lean_array_get(x_58, x_2, x_48);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Expr_getAppNumArgsAux(x_5, x_60);
lean_inc(x_61);
x_62 = lean_mk_array(x_61, x_1);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_61, x_63);
lean_dec(x_61);
x_65 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_62, x_64);
x_66 = l_Lean_mkAppN(x_59, x_65);
lean_dec(x_65);
x_67 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_68 = l_Array_ofSubarray___rarg(x_67);
lean_dec(x_67);
x_69 = l_Lean_mkAppN(x_66, x_68);
lean_dec(x_68);
x_70 = l_Lean_Expr_headBeta(x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_48);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_16);
return x_74;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_mkAppN(x_1, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Meta_whnf(x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_getAppFn(x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_array_get_size(x_7);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
lean_inc(x_16);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_3, x_4, x_5, x_6, x_16, x_18, x_19, x_7, x_22, x_23, x_20, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_reduceMatcher_x3f___lambda__1(x_16, x_28, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_24, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_32);
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Meta_getMatcherInfo_x3f(x_8, x_2, x_3, x_4, x_5, x_6);
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
x_25 = l_Lean_Expr_getAppArgs___closed__1;
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
x_38 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_8, x_2, x_3, x_4, x_5, x_19);
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
lean_dec(x_42);
x_44 = l_Lean_mkAppN(x_41, x_43);
lean_dec(x_43);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_44);
x_45 = l_Lean_Meta_inferType(x_44, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_ctor_set(x_11, 0, x_35);
x_48 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed), 13, 6);
lean_closure_set(x_48, 0, x_44);
lean_closure_set(x_48, 1, x_33);
lean_closure_set(x_48, 2, x_25);
lean_closure_set(x_48, 3, x_29);
lean_closure_set(x_48, 4, x_34);
lean_closure_set(x_48, 5, x_36);
x_49 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_46, x_11, x_48, x_2, x_3, x_4, x_5, x_47);
return x_49;
}
else
{
uint8_t x_50; 
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
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
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
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
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
x_58 = lean_box(3);
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_62 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_61);
x_63 = lean_mk_array(x_61, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_61, x_64);
lean_dec(x_61);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_nat_add(x_67, x_64);
lean_dec(x_67);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
x_70 = lean_nat_add(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
x_71 = lean_array_get_size(x_66);
x_72 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_59);
lean_dec(x_59);
x_73 = lean_nat_add(x_70, x_72);
x_74 = lean_nat_dec_lt(x_71, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_free_object(x_10);
x_75 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_8, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_instantiate_value_lparams(x_76, x_9);
lean_dec(x_9);
lean_dec(x_76);
lean_inc(x_70);
lean_inc(x_66);
x_79 = l_Array_toSubarray___rarg(x_66, x_60, x_70);
x_80 = l_Array_ofSubarray___rarg(x_79);
lean_dec(x_79);
x_81 = l_Lean_mkAppN(x_78, x_80);
lean_dec(x_80);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_81);
x_82 = l_Lean_Meta_inferType(x_81, x_2, x_3, x_4, x_5, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_72);
x_86 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed), 13, 6);
lean_closure_set(x_86, 0, x_81);
lean_closure_set(x_86, 1, x_70);
lean_closure_set(x_86, 2, x_62);
lean_closure_set(x_86, 3, x_66);
lean_closure_set(x_86, 4, x_71);
lean_closure_set(x_86, 5, x_73);
x_87 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_83, x_85, x_86, x_2, x_3, x_4, x_5, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
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
else
{
lean_object* x_96; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_box(3);
lean_ctor_set(x_10, 0, x_96);
return x_10;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_97 = lean_ctor_get(x_10, 1);
lean_inc(x_97);
lean_dec(x_10);
x_98 = lean_ctor_get(x_11, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_99 = x_11;
} else {
 lean_dec_ref(x_11);
 x_99 = lean_box(0);
}
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Expr_getAppNumArgsAux(x_1, x_100);
x_102 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_101);
x_103 = lean_mk_array(x_101, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_101, x_104);
lean_dec(x_101);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_105);
x_107 = lean_ctor_get(x_98, 0);
lean_inc(x_107);
x_108 = lean_nat_add(x_107, x_104);
lean_dec(x_107);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
x_110 = lean_nat_add(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
x_111 = lean_array_get_size(x_106);
x_112 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_98);
lean_dec(x_98);
x_113 = lean_nat_add(x_110, x_112);
x_114 = lean_nat_dec_lt(x_111, x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_8, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_instantiate_value_lparams(x_116, x_9);
lean_dec(x_9);
lean_dec(x_116);
lean_inc(x_110);
lean_inc(x_106);
x_119 = l_Array_toSubarray___rarg(x_106, x_100, x_110);
x_120 = l_Array_ofSubarray___rarg(x_119);
lean_dec(x_119);
x_121 = l_Lean_mkAppN(x_118, x_120);
lean_dec(x_120);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_121);
x_122 = l_Lean_Meta_inferType(x_121, x_2, x_3, x_4, x_5, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
if (lean_is_scalar(x_99)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_99;
}
lean_ctor_set(x_125, 0, x_112);
x_126 = lean_alloc_closure((void*)(l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed), 13, 6);
lean_closure_set(x_126, 0, x_121);
lean_closure_set(x_126, 1, x_110);
lean_closure_set(x_126, 2, x_102);
lean_closure_set(x_126, 3, x_106);
lean_closure_set(x_126, 4, x_111);
lean_closure_set(x_126, 5, x_113);
x_127 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_123, x_125, x_126, x_2, x_3, x_4, x_5, x_124);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_121);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_122, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_130 = x_122;
} else {
 lean_dec_ref(x_122);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_box(3);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_97);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_box(2);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_6);
return x_139;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_18, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
return x_19;
}
}
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_reduceMatcher_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_reduceMatcher_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
lean_object* l_Lean_Meta_project_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Meta_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_11);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_environment_find(x_17, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_10);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_21) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux(x_10, x_23);
x_25 = lean_ctor_get(x_22, 3);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_nat_add(x_25, x_2);
lean_dec(x_25);
x_27 = lean_nat_dec_lt(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_10);
x_28 = lean_box(0);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_nat_sub(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_32 = l_Lean_Expr_getRevArg_x21(x_10, x_31);
lean_dec(x_10);
lean_ctor_set(x_18, 0, x_32);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
}
else
{
lean_object* x_33; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_10);
x_33 = lean_box(0);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
if (lean_obj_tag(x_34) == 6)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux(x_10, x_36);
x_38 = lean_ctor_get(x_35, 3);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_nat_add(x_38, x_2);
lean_dec(x_38);
x_40 = lean_nat_dec_lt(x_39, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_10);
x_41 = lean_box(0);
lean_ctor_set(x_14, 0, x_41);
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_nat_sub(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_42, x_43);
lean_dec(x_42);
x_45 = l_Lean_Expr_getRevArg_x21(x_10, x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_10);
x_47 = lean_box(0);
lean_ctor_set(x_14, 0, x_47);
return x_14;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_environment_find(x_50, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
if (lean_obj_tag(x_54) == 6)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Expr_getAppNumArgsAux(x_10, x_57);
x_59 = lean_ctor_get(x_56, 3);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_nat_add(x_59, x_2);
lean_dec(x_59);
x_61 = lean_nat_dec_lt(x_60, x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_10);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_nat_sub(x_58, x_60);
lean_dec(x_60);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_64, x_65);
lean_dec(x_64);
x_67 = l_Lean_Expr_getRevArg_x21(x_10, x_66);
lean_dec(x_10);
if (lean_is_scalar(x_55)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_55;
}
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_49);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_10);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_49);
return x_71;
}
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
x_72 = lean_box(0);
lean_ctor_set(x_8, 0, x_72);
return x_8;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_75 = l_Lean_Expr_getAppFn(x_73);
if (lean_obj_tag(x_75) == 4)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_6, x_74);
lean_dec(x_6);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_environment_find(x_81, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_73);
x_83 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_86 = x_82;
} else {
 lean_dec_ref(x_82);
 x_86 = lean_box(0);
}
if (lean_obj_tag(x_85) == 6)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Expr_getAppNumArgsAux(x_73, x_88);
x_90 = lean_ctor_get(x_87, 3);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_nat_add(x_90, x_2);
lean_dec(x_90);
x_92 = lean_nat_dec_lt(x_91, x_89);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_73);
x_93 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_80;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_79);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_nat_sub(x_89, x_91);
lean_dec(x_91);
lean_dec(x_89);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_95, x_96);
lean_dec(x_95);
x_98 = l_Lean_Expr_getRevArg_x21(x_73, x_97);
lean_dec(x_73);
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_80)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_80;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_79);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_73);
x_101 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_80;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_79);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_6);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_74);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_6);
x_105 = !lean_is_exclusive(x_8);
if (x_105 == 0)
{
return x_8;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_8, 0);
x_107 = lean_ctor_get(x_8, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_8);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
lean_object* l_Lean_Meta_project_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_project_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_reduceProj_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 11)
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
lean_object* l_Lean_Meta_reduceProj_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_whnfCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_4, x_1, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 7:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_whnfCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_5, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_whnfCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfCore_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfCore_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfCore_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_3(x_2, x_7, x_8, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
case 8:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_5(x_3, x_17, x_18, x_19, x_20, x_22);
return x_23;
}
case 11:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_4(x_5, x_24, x_25, x_26, x_28);
return x_29;
}
default: 
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_apply_1(x_6, x_1);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_whnfCore_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore_match__4___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l_Lean_ConstantInfo_lparams(x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthAux___rarg(x_12, x_13);
lean_dec(x_12);
x_15 = l_List_lengthAux___rarg(x_5, x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_expr_eqv(x_2, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_updateFn(x_1, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_instantiate_value_lparams(x_4, x_5);
x_22 = l_Lean_Expr_betaRev(x_21, x_6);
lean_dec(x_21);
x_23 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_22);
x_24 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_23, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_expr_eqv(x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_updateFn(x_3, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.whnfCore");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(341u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_562____closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
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
x_36 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_34, x_11, x_35);
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
x_45 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_42, x_11, x_44);
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
x_70 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_66, x_11, x_69);
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
lean_object* x_94; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_227 = lean_st_ref_get(x_5, x_6);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 3);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get_uint8(x_229, sizeof(void*)*1);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_dec(x_227);
x_94 = x_231;
goto block_226;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_dec(x_227);
x_233 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
x_234 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_233, x_2, x_3, x_4, x_5, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_94 = x_237;
goto block_226;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
lean_dec(x_234);
lean_inc(x_1);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_1);
x_240 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_233, x_239, x_2, x_3, x_4, x_5, x_238);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_94 = x_241;
goto block_226;
}
}
block_226:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
case 5:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = l_Lean_Expr_getAppFn(x_96);
lean_dec(x_96);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_97);
x_98 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_97, x_2, x_3, x_4, x_5, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Expr_isLambda(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_102 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
switch (lean_obj_tag(x_103)) {
case 0:
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_1);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_1 = x_105;
x_6 = x_104;
goto _start;
}
case 2:
{
if (lean_obj_tag(x_99) == 4)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
lean_inc(x_1);
lean_inc(x_99);
lean_inc(x_97);
x_110 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_110, 0, x_97);
lean_closure_set(x_110, 1, x_99);
lean_closure_set(x_110, 2, x_1);
x_111 = l_Lean_Meta_getConst_x3f(x_108, x_2, x_3, x_4, x_5, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
x_115 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
lean_ctor_set(x_111, 0, x_116);
return x_111;
}
else
{
lean_dec(x_99);
lean_ctor_set(x_111, 0, x_1);
return x_111;
}
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_dec(x_111);
x_118 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; 
lean_dec(x_99);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_117);
return x_121;
}
}
}
else
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_112, 0);
lean_inc(x_122);
lean_dec(x_112);
switch (lean_obj_tag(x_122)) {
case 1:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_110);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
lean_dec(x_111);
x_124 = l_Lean_ConstantInfo_name(x_122);
x_125 = l_Lean_Meta_isAuxDef(x_124, x_2, x_3, x_4, x_5, x_123);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
uint8_t x_128; 
lean_dec(x_122);
lean_dec(x_109);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_125);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_125, 0);
lean_dec(x_129);
x_130 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
lean_ctor_set(x_125, 0, x_131);
return x_125;
}
else
{
lean_dec(x_99);
lean_ctor_set(x_125, 0, x_1);
return x_125;
}
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_125, 1);
lean_inc(x_132);
lean_dec(x_125);
x_133 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_99);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_1);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
lean_dec(x_125);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Lean_Expr_getAppNumArgsAux(x_1, x_138);
x_140 = lean_mk_empty_array_with_capacity(x_139);
lean_dec(x_139);
lean_inc(x_1);
x_141 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_140);
x_142 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_1, x_97, x_99, x_122, x_109, x_141, x_2, x_3, x_4, x_5, x_137);
lean_dec(x_141);
lean_dec(x_109);
lean_dec(x_122);
lean_dec(x_99);
lean_dec(x_97);
return x_142;
}
}
case 4:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_99);
lean_dec(x_97);
x_143 = lean_ctor_get(x_111, 1);
lean_inc(x_143);
lean_dec(x_111);
x_144 = lean_ctor_get(x_122, 0);
lean_inc(x_144);
lean_dec(x_122);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Expr_getAppNumArgsAux(x_1, x_145);
x_147 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_146);
x_148 = lean_mk_array(x_146, x_147);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_sub(x_146, x_149);
lean_dec(x_146);
x_151 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_148, x_150);
x_152 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_153 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_144, x_109, x_151, x_110, x_152, x_2, x_3, x_4, x_5, x_143);
lean_dec(x_151);
lean_dec(x_109);
lean_dec(x_144);
return x_153;
}
case 7:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_99);
lean_dec(x_97);
x_154 = lean_ctor_get(x_111, 1);
lean_inc(x_154);
lean_dec(x_111);
x_155 = lean_ctor_get(x_122, 0);
lean_inc(x_155);
lean_dec(x_122);
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Expr_getAppNumArgsAux(x_1, x_156);
x_158 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_157);
x_159 = lean_mk_array(x_157, x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_sub(x_157, x_160);
lean_dec(x_157);
x_162 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_159, x_161);
x_163 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_164 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_155, x_109, x_162, x_110, x_163, x_2, x_3, x_4, x_5, x_154);
lean_dec(x_162);
lean_dec(x_109);
return x_164;
}
default: 
{
uint8_t x_165; 
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_111);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_111, 0);
lean_dec(x_166);
x_167 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
lean_ctor_set(x_111, 0, x_168);
return x_111;
}
else
{
lean_dec(x_99);
lean_ctor_set(x_111, 0, x_1);
return x_111;
}
}
else
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_111, 1);
lean_inc(x_169);
lean_dec(x_111);
x_170 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_99);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_169);
return x_173;
}
}
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_111);
if (x_174 == 0)
{
return x_111;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_111, 0);
x_176 = lean_ctor_get(x_111, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_111);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_102);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_102, 0);
lean_dec(x_179);
x_180 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
lean_ctor_set(x_102, 0, x_181);
return x_102;
}
else
{
lean_dec(x_99);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
}
else
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_102, 1);
lean_inc(x_182);
lean_dec(x_102);
x_183 = lean_expr_eqv(x_97, x_99);
lean_dec(x_97);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_Lean_Expr_updateFn(x_1, x_99);
lean_dec(x_99);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_99);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_182);
return x_186;
}
}
}
}
default: 
{
uint8_t x_187; 
lean_dec(x_103);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_102);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_102, 0);
lean_dec(x_188);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_102, 1);
lean_inc(x_189);
lean_dec(x_102);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_102);
if (x_191 == 0)
{
return x_102;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_102, 0);
x_193 = lean_ctor_get(x_102, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_102);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_97);
x_195 = lean_unsigned_to_nat(0u);
x_196 = l_Lean_Expr_getAppNumArgsAux(x_1, x_195);
x_197 = lean_mk_empty_array_with_capacity(x_196);
lean_dec(x_196);
x_198 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_197);
x_199 = l_Lean_Expr_betaRev(x_99, x_198);
lean_dec(x_198);
lean_dec(x_99);
x_1 = x_199;
x_6 = x_100;
goto _start;
}
}
else
{
uint8_t x_201; 
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_98);
if (x_201 == 0)
{
return x_98;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_98, 0);
x_203 = lean_ctor_get(x_98, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_98);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 8:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_1, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_1, 3);
lean_inc(x_206);
lean_dec(x_1);
x_207 = lean_expr_instantiate1(x_206, x_205);
lean_dec(x_205);
lean_dec(x_206);
x_1 = x_207;
x_6 = x_94;
goto _start;
}
case 11:
{
lean_object* x_209; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_209 = l_Lean_Meta_reduceProj_x3f(x_1, x_2, x_3, x_4, x_5, x_94);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_209);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_209, 0);
lean_dec(x_212);
lean_ctor_set(x_209, 0, x_1);
return x_209;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_dec(x_209);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_1);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_1);
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_dec(x_209);
x_216 = lean_ctor_get(x_210, 0);
lean_inc(x_216);
lean_dec(x_210);
x_1 = x_216;
x_6 = x_215;
goto _start;
}
}
else
{
uint8_t x_218; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_209);
if (x_218 == 0)
{
return x_209;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_209, 0);
x_220 = lean_ctor_get(x_209, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_209);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
default: 
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_1);
x_222 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_223 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_224 = lean_panic_fn(x_222, x_223);
x_225 = lean_apply_5(x_224, x_2, x_3, x_4, x_5, x_94);
return x_225;
}
}
}
}
case 5:
{
lean_object* x_242; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_375 = lean_st_ref_get(x_5, x_6);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_376, 3);
lean_inc(x_377);
lean_dec(x_376);
x_378 = lean_ctor_get_uint8(x_377, sizeof(void*)*1);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_375, 1);
lean_inc(x_379);
lean_dec(x_375);
x_242 = x_379;
goto block_374;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
lean_dec(x_375);
x_381 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
x_382 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_381, x_2, x_3, x_4, x_5, x_380);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
x_242 = x_385;
goto block_374;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
lean_dec(x_382);
lean_inc(x_1);
x_387 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_387, 0, x_1);
x_388 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_381, x_387, x_2, x_3, x_4, x_5, x_386);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_242 = x_389;
goto block_374;
}
}
block_374:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_243; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
case 5:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_1, 0);
lean_inc(x_244);
x_245 = l_Lean_Expr_getAppFn(x_244);
lean_dec(x_244);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_245);
x_246 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_245, x_2, x_3, x_4, x_5, x_242);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_Expr_isLambda(x_247);
if (x_249 == 0)
{
lean_object* x_250; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_250 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_248);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
switch (lean_obj_tag(x_251)) {
case 0:
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_1);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
lean_dec(x_251);
x_1 = x_253;
x_6 = x_252;
goto _start;
}
case 2:
{
if (lean_obj_tag(x_247) == 4)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_250, 1);
lean_inc(x_255);
lean_dec(x_250);
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_247, 1);
lean_inc(x_257);
lean_inc(x_1);
lean_inc(x_247);
lean_inc(x_245);
x_258 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_258, 0, x_245);
lean_closure_set(x_258, 1, x_247);
lean_closure_set(x_258, 2, x_1);
x_259 = l_Lean_Meta_getConst_x3f(x_256, x_2, x_3, x_4, x_5, x_255);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = !lean_is_exclusive(x_259);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_259, 0);
lean_dec(x_262);
x_263 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
lean_ctor_set(x_259, 0, x_264);
return x_259;
}
else
{
lean_dec(x_247);
lean_ctor_set(x_259, 0, x_1);
return x_259;
}
}
else
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_259, 1);
lean_inc(x_265);
lean_dec(x_259);
x_266 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_265);
return x_268;
}
else
{
lean_object* x_269; 
lean_dec(x_247);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_1);
lean_ctor_set(x_269, 1, x_265);
return x_269;
}
}
}
else
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_260, 0);
lean_inc(x_270);
lean_dec(x_260);
switch (lean_obj_tag(x_270)) {
case 1:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_258);
x_271 = lean_ctor_get(x_259, 1);
lean_inc(x_271);
lean_dec(x_259);
x_272 = l_Lean_ConstantInfo_name(x_270);
x_273 = l_Lean_Meta_isAuxDef(x_272, x_2, x_3, x_4, x_5, x_271);
lean_dec(x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
lean_dec(x_274);
if (x_275 == 0)
{
uint8_t x_276; 
lean_dec(x_270);
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_276 = !lean_is_exclusive(x_273);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_273, 0);
lean_dec(x_277);
x_278 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
lean_ctor_set(x_273, 0, x_279);
return x_273;
}
else
{
lean_dec(x_247);
lean_ctor_set(x_273, 0, x_1);
return x_273;
}
}
else
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_ctor_get(x_273, 1);
lean_inc(x_280);
lean_dec(x_273);
x_281 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
return x_283;
}
else
{
lean_object* x_284; 
lean_dec(x_247);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_1);
lean_ctor_set(x_284, 1, x_280);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_285 = lean_ctor_get(x_273, 1);
lean_inc(x_285);
lean_dec(x_273);
x_286 = lean_unsigned_to_nat(0u);
x_287 = l_Lean_Expr_getAppNumArgsAux(x_1, x_286);
x_288 = lean_mk_empty_array_with_capacity(x_287);
lean_dec(x_287);
lean_inc(x_1);
x_289 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_288);
x_290 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_1, x_245, x_247, x_270, x_257, x_289, x_2, x_3, x_4, x_5, x_285);
lean_dec(x_289);
lean_dec(x_257);
lean_dec(x_270);
lean_dec(x_247);
lean_dec(x_245);
return x_290;
}
}
case 4:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_247);
lean_dec(x_245);
x_291 = lean_ctor_get(x_259, 1);
lean_inc(x_291);
lean_dec(x_259);
x_292 = lean_ctor_get(x_270, 0);
lean_inc(x_292);
lean_dec(x_270);
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Lean_Expr_getAppNumArgsAux(x_1, x_293);
x_295 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_294);
x_296 = lean_mk_array(x_294, x_295);
x_297 = lean_unsigned_to_nat(1u);
x_298 = lean_nat_sub(x_294, x_297);
lean_dec(x_294);
x_299 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_296, x_298);
x_300 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_301 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_292, x_257, x_299, x_258, x_300, x_2, x_3, x_4, x_5, x_291);
lean_dec(x_299);
lean_dec(x_257);
lean_dec(x_292);
return x_301;
}
case 7:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_247);
lean_dec(x_245);
x_302 = lean_ctor_get(x_259, 1);
lean_inc(x_302);
lean_dec(x_259);
x_303 = lean_ctor_get(x_270, 0);
lean_inc(x_303);
lean_dec(x_270);
x_304 = lean_unsigned_to_nat(0u);
x_305 = l_Lean_Expr_getAppNumArgsAux(x_1, x_304);
x_306 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_305);
x_307 = lean_mk_array(x_305, x_306);
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_nat_sub(x_305, x_308);
lean_dec(x_305);
x_310 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_307, x_309);
x_311 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_312 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_303, x_257, x_310, x_258, x_311, x_2, x_3, x_4, x_5, x_302);
lean_dec(x_310);
lean_dec(x_257);
return x_312;
}
default: 
{
uint8_t x_313; 
lean_dec(x_270);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_313 = !lean_is_exclusive(x_259);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_259, 0);
lean_dec(x_314);
x_315 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_315 == 0)
{
lean_object* x_316; 
x_316 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
lean_ctor_set(x_259, 0, x_316);
return x_259;
}
else
{
lean_dec(x_247);
lean_ctor_set(x_259, 0, x_1);
return x_259;
}
}
else
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_259, 1);
lean_inc(x_317);
lean_dec(x_259);
x_318 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_317);
return x_320;
}
else
{
lean_object* x_321; 
lean_dec(x_247);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_1);
lean_ctor_set(x_321, 1, x_317);
return x_321;
}
}
}
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_259);
if (x_322 == 0)
{
return x_259;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_259, 0);
x_324 = lean_ctor_get(x_259, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_259);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_250);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_250, 0);
lean_dec(x_327);
x_328 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_328 == 0)
{
lean_object* x_329; 
x_329 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
lean_ctor_set(x_250, 0, x_329);
return x_250;
}
else
{
lean_dec(x_247);
lean_ctor_set(x_250, 0, x_1);
return x_250;
}
}
else
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_250, 1);
lean_inc(x_330);
lean_dec(x_250);
x_331 = lean_expr_eqv(x_245, x_247);
lean_dec(x_245);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = l_Lean_Expr_updateFn(x_1, x_247);
lean_dec(x_247);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_330);
return x_333;
}
else
{
lean_object* x_334; 
lean_dec(x_247);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_1);
lean_ctor_set(x_334, 1, x_330);
return x_334;
}
}
}
}
default: 
{
uint8_t x_335; 
lean_dec(x_251);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = !lean_is_exclusive(x_250);
if (x_335 == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_250, 0);
lean_dec(x_336);
lean_ctor_set(x_250, 0, x_1);
return x_250;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_250, 1);
lean_inc(x_337);
lean_dec(x_250);
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
uint8_t x_339; 
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_250);
if (x_339 == 0)
{
return x_250;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_250, 0);
x_341 = lean_ctor_get(x_250, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_250);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_245);
x_343 = lean_unsigned_to_nat(0u);
x_344 = l_Lean_Expr_getAppNumArgsAux(x_1, x_343);
x_345 = lean_mk_empty_array_with_capacity(x_344);
lean_dec(x_344);
x_346 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_345);
x_347 = l_Lean_Expr_betaRev(x_247, x_346);
lean_dec(x_346);
lean_dec(x_247);
x_1 = x_347;
x_6 = x_248;
goto _start;
}
}
else
{
uint8_t x_349; 
lean_dec(x_245);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_246);
if (x_349 == 0)
{
return x_246;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_246, 0);
x_351 = lean_ctor_get(x_246, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_246);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
case 8:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_1, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_1, 3);
lean_inc(x_354);
lean_dec(x_1);
x_355 = lean_expr_instantiate1(x_354, x_353);
lean_dec(x_353);
lean_dec(x_354);
x_1 = x_355;
x_6 = x_242;
goto _start;
}
case 11:
{
lean_object* x_357; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_357 = l_Lean_Meta_reduceProj_x3f(x_1, x_2, x_3, x_4, x_5, x_242);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = !lean_is_exclusive(x_357);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_357, 0);
lean_dec(x_360);
lean_ctor_set(x_357, 0, x_1);
return x_357;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_1);
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_dec(x_357);
x_364 = lean_ctor_get(x_358, 0);
lean_inc(x_364);
lean_dec(x_358);
x_1 = x_364;
x_6 = x_363;
goto _start;
}
}
else
{
uint8_t x_366; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_366 = !lean_is_exclusive(x_357);
if (x_366 == 0)
{
return x_357;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_357, 0);
x_368 = lean_ctor_get(x_357, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_357);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
default: 
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_1);
x_370 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_371 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_372 = lean_panic_fn(x_370, x_371);
x_373 = lean_apply_5(x_372, x_2, x_3, x_4, x_5, x_242);
return x_373;
}
}
}
}
case 8:
{
lean_object* x_390; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_523 = lean_st_ref_get(x_5, x_6);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_524, 3);
lean_inc(x_525);
lean_dec(x_524);
x_526 = lean_ctor_get_uint8(x_525, sizeof(void*)*1);
lean_dec(x_525);
if (x_526 == 0)
{
lean_object* x_527; 
x_527 = lean_ctor_get(x_523, 1);
lean_inc(x_527);
lean_dec(x_523);
x_390 = x_527;
goto block_522;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_528 = lean_ctor_get(x_523, 1);
lean_inc(x_528);
lean_dec(x_523);
x_529 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
x_530 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_529, x_2, x_3, x_4, x_5, x_528);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_unbox(x_531);
lean_dec(x_531);
if (x_532 == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_530, 1);
lean_inc(x_533);
lean_dec(x_530);
x_390 = x_533;
goto block_522;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_530, 1);
lean_inc(x_534);
lean_dec(x_530);
lean_inc(x_1);
x_535 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_535, 0, x_1);
x_536 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_529, x_535, x_2, x_3, x_4, x_5, x_534);
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
x_390 = x_537;
goto block_522;
}
}
block_522:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_391; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_1);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
case 5:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_1, 0);
lean_inc(x_392);
x_393 = l_Lean_Expr_getAppFn(x_392);
lean_dec(x_392);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_393);
x_394 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_393, x_2, x_3, x_4, x_5, x_390);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = l_Lean_Expr_isLambda(x_395);
if (x_397 == 0)
{
lean_object* x_398; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_396);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
switch (lean_obj_tag(x_399)) {
case 0:
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_1);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
lean_dec(x_399);
x_1 = x_401;
x_6 = x_400;
goto _start;
}
case 2:
{
if (lean_obj_tag(x_395) == 4)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
lean_dec(x_398);
x_404 = lean_ctor_get(x_395, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_395, 1);
lean_inc(x_405);
lean_inc(x_1);
lean_inc(x_395);
lean_inc(x_393);
x_406 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_406, 0, x_393);
lean_closure_set(x_406, 1, x_395);
lean_closure_set(x_406, 2, x_1);
x_407 = l_Lean_Meta_getConst_x3f(x_404, x_2, x_3, x_4, x_5, x_403);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_obj_tag(x_408) == 0)
{
uint8_t x_409; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_409 = !lean_is_exclusive(x_407);
if (x_409 == 0)
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_407, 0);
lean_dec(x_410);
x_411 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_411 == 0)
{
lean_object* x_412; 
x_412 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
lean_ctor_set(x_407, 0, x_412);
return x_407;
}
else
{
lean_dec(x_395);
lean_ctor_set(x_407, 0, x_1);
return x_407;
}
}
else
{
lean_object* x_413; uint8_t x_414; 
x_413 = lean_ctor_get(x_407, 1);
lean_inc(x_413);
lean_dec(x_407);
x_414 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_413);
return x_416;
}
else
{
lean_object* x_417; 
lean_dec(x_395);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_1);
lean_ctor_set(x_417, 1, x_413);
return x_417;
}
}
}
else
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_408, 0);
lean_inc(x_418);
lean_dec(x_408);
switch (lean_obj_tag(x_418)) {
case 1:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_406);
x_419 = lean_ctor_get(x_407, 1);
lean_inc(x_419);
lean_dec(x_407);
x_420 = l_Lean_ConstantInfo_name(x_418);
x_421 = l_Lean_Meta_isAuxDef(x_420, x_2, x_3, x_4, x_5, x_419);
lean_dec(x_420);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_unbox(x_422);
lean_dec(x_422);
if (x_423 == 0)
{
uint8_t x_424; 
lean_dec(x_418);
lean_dec(x_405);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_424 = !lean_is_exclusive(x_421);
if (x_424 == 0)
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_ctor_get(x_421, 0);
lean_dec(x_425);
x_426 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
lean_ctor_set(x_421, 0, x_427);
return x_421;
}
else
{
lean_dec(x_395);
lean_ctor_set(x_421, 0, x_1);
return x_421;
}
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = lean_ctor_get(x_421, 1);
lean_inc(x_428);
lean_dec(x_421);
x_429 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_428);
return x_431;
}
else
{
lean_object* x_432; 
lean_dec(x_395);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_1);
lean_ctor_set(x_432, 1, x_428);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_433 = lean_ctor_get(x_421, 1);
lean_inc(x_433);
lean_dec(x_421);
x_434 = lean_unsigned_to_nat(0u);
x_435 = l_Lean_Expr_getAppNumArgsAux(x_1, x_434);
x_436 = lean_mk_empty_array_with_capacity(x_435);
lean_dec(x_435);
lean_inc(x_1);
x_437 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_436);
x_438 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_1, x_393, x_395, x_418, x_405, x_437, x_2, x_3, x_4, x_5, x_433);
lean_dec(x_437);
lean_dec(x_405);
lean_dec(x_418);
lean_dec(x_395);
lean_dec(x_393);
return x_438;
}
}
case 4:
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_395);
lean_dec(x_393);
x_439 = lean_ctor_get(x_407, 1);
lean_inc(x_439);
lean_dec(x_407);
x_440 = lean_ctor_get(x_418, 0);
lean_inc(x_440);
lean_dec(x_418);
x_441 = lean_unsigned_to_nat(0u);
x_442 = l_Lean_Expr_getAppNumArgsAux(x_1, x_441);
x_443 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_442);
x_444 = lean_mk_array(x_442, x_443);
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_nat_sub(x_442, x_445);
lean_dec(x_442);
x_447 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_444, x_446);
x_448 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_449 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_440, x_405, x_447, x_406, x_448, x_2, x_3, x_4, x_5, x_439);
lean_dec(x_447);
lean_dec(x_405);
lean_dec(x_440);
return x_449;
}
case 7:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_395);
lean_dec(x_393);
x_450 = lean_ctor_get(x_407, 1);
lean_inc(x_450);
lean_dec(x_407);
x_451 = lean_ctor_get(x_418, 0);
lean_inc(x_451);
lean_dec(x_418);
x_452 = lean_unsigned_to_nat(0u);
x_453 = l_Lean_Expr_getAppNumArgsAux(x_1, x_452);
x_454 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_453);
x_455 = lean_mk_array(x_453, x_454);
x_456 = lean_unsigned_to_nat(1u);
x_457 = lean_nat_sub(x_453, x_456);
lean_dec(x_453);
x_458 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_455, x_457);
x_459 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_460 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_451, x_405, x_458, x_406, x_459, x_2, x_3, x_4, x_5, x_450);
lean_dec(x_458);
lean_dec(x_405);
return x_460;
}
default: 
{
uint8_t x_461; 
lean_dec(x_418);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_461 = !lean_is_exclusive(x_407);
if (x_461 == 0)
{
lean_object* x_462; uint8_t x_463; 
x_462 = lean_ctor_get(x_407, 0);
lean_dec(x_462);
x_463 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_463 == 0)
{
lean_object* x_464; 
x_464 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
lean_ctor_set(x_407, 0, x_464);
return x_407;
}
else
{
lean_dec(x_395);
lean_ctor_set(x_407, 0, x_1);
return x_407;
}
}
else
{
lean_object* x_465; uint8_t x_466; 
x_465 = lean_ctor_get(x_407, 1);
lean_inc(x_465);
lean_dec(x_407);
x_466 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_465);
return x_468;
}
else
{
lean_object* x_469; 
lean_dec(x_395);
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_1);
lean_ctor_set(x_469, 1, x_465);
return x_469;
}
}
}
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_470 = !lean_is_exclusive(x_407);
if (x_470 == 0)
{
return x_407;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_407, 0);
x_472 = lean_ctor_get(x_407, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_407);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_474 = !lean_is_exclusive(x_398);
if (x_474 == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_ctor_get(x_398, 0);
lean_dec(x_475);
x_476 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_476 == 0)
{
lean_object* x_477; 
x_477 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
lean_ctor_set(x_398, 0, x_477);
return x_398;
}
else
{
lean_dec(x_395);
lean_ctor_set(x_398, 0, x_1);
return x_398;
}
}
else
{
lean_object* x_478; uint8_t x_479; 
x_478 = lean_ctor_get(x_398, 1);
lean_inc(x_478);
lean_dec(x_398);
x_479 = lean_expr_eqv(x_393, x_395);
lean_dec(x_393);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
x_480 = l_Lean_Expr_updateFn(x_1, x_395);
lean_dec(x_395);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_478);
return x_481;
}
else
{
lean_object* x_482; 
lean_dec(x_395);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_1);
lean_ctor_set(x_482, 1, x_478);
return x_482;
}
}
}
}
default: 
{
uint8_t x_483; 
lean_dec(x_399);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_483 = !lean_is_exclusive(x_398);
if (x_483 == 0)
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_398, 0);
lean_dec(x_484);
lean_ctor_set(x_398, 0, x_1);
return x_398;
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_398, 1);
lean_inc(x_485);
lean_dec(x_398);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_1);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_398);
if (x_487 == 0)
{
return x_398;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_398, 0);
x_489 = lean_ctor_get(x_398, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_398);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_393);
x_491 = lean_unsigned_to_nat(0u);
x_492 = l_Lean_Expr_getAppNumArgsAux(x_1, x_491);
x_493 = lean_mk_empty_array_with_capacity(x_492);
lean_dec(x_492);
x_494 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_493);
x_495 = l_Lean_Expr_betaRev(x_395, x_494);
lean_dec(x_494);
lean_dec(x_395);
x_1 = x_495;
x_6 = x_396;
goto _start;
}
}
else
{
uint8_t x_497; 
lean_dec(x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = !lean_is_exclusive(x_394);
if (x_497 == 0)
{
return x_394;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_394, 0);
x_499 = lean_ctor_get(x_394, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_394);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
case 8:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_1, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_1, 3);
lean_inc(x_502);
lean_dec(x_1);
x_503 = lean_expr_instantiate1(x_502, x_501);
lean_dec(x_501);
lean_dec(x_502);
x_1 = x_503;
x_6 = x_390;
goto _start;
}
case 11:
{
lean_object* x_505; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_505 = l_Lean_Meta_reduceProj_x3f(x_1, x_2, x_3, x_4, x_5, x_390);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_obj_tag(x_506) == 0)
{
uint8_t x_507; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_507 = !lean_is_exclusive(x_505);
if (x_507 == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_505, 0);
lean_dec(x_508);
lean_ctor_set(x_505, 0, x_1);
return x_505;
}
else
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_505, 1);
lean_inc(x_509);
lean_dec(x_505);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_1);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; 
lean_dec(x_1);
x_511 = lean_ctor_get(x_505, 1);
lean_inc(x_511);
lean_dec(x_505);
x_512 = lean_ctor_get(x_506, 0);
lean_inc(x_512);
lean_dec(x_506);
x_1 = x_512;
x_6 = x_511;
goto _start;
}
}
else
{
uint8_t x_514; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_514 = !lean_is_exclusive(x_505);
if (x_514 == 0)
{
return x_505;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_505, 0);
x_516 = lean_ctor_get(x_505, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_505);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
default: 
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_1);
x_518 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_519 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_520 = lean_panic_fn(x_518, x_519);
x_521 = lean_apply_5(x_520, x_2, x_3, x_4, x_5, x_390);
return x_521;
}
}
}
}
case 10:
{
lean_object* x_538; 
x_538 = lean_ctor_get(x_1, 1);
lean_inc(x_538);
lean_dec(x_1);
x_1 = x_538;
goto _start;
}
case 11:
{
lean_object* x_540; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_673 = lean_st_ref_get(x_5, x_6);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_674, 3);
lean_inc(x_675);
lean_dec(x_674);
x_676 = lean_ctor_get_uint8(x_675, sizeof(void*)*1);
lean_dec(x_675);
if (x_676 == 0)
{
lean_object* x_677; 
x_677 = lean_ctor_get(x_673, 1);
lean_inc(x_677);
lean_dec(x_673);
x_540 = x_677;
goto block_672;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_678 = lean_ctor_get(x_673, 1);
lean_inc(x_678);
lean_dec(x_673);
x_679 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
x_680 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_679, x_2, x_3, x_4, x_5, x_678);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_unbox(x_681);
lean_dec(x_681);
if (x_682 == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_680, 1);
lean_inc(x_683);
lean_dec(x_680);
x_540 = x_683;
goto block_672;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_684 = lean_ctor_get(x_680, 1);
lean_inc(x_684);
lean_dec(x_680);
lean_inc(x_1);
x_685 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_685, 0, x_1);
x_686 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_679, x_685, x_2, x_3, x_4, x_5, x_684);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
x_540 = x_687;
goto block_672;
}
}
block_672:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_541; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_1);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
case 5:
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_1, 0);
lean_inc(x_542);
x_543 = l_Lean_Expr_getAppFn(x_542);
lean_dec(x_542);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_543);
x_544 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_543, x_2, x_3, x_4, x_5, x_540);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; uint8_t x_547; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = l_Lean_Expr_isLambda(x_545);
if (x_547 == 0)
{
lean_object* x_548; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_548 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_2, x_3, x_4, x_5, x_546);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
switch (lean_obj_tag(x_549)) {
case 0:
{
lean_object* x_550; lean_object* x_551; 
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_1);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
lean_dec(x_549);
x_1 = x_551;
x_6 = x_550;
goto _start;
}
case 2:
{
if (lean_obj_tag(x_545) == 4)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_548, 1);
lean_inc(x_553);
lean_dec(x_548);
x_554 = lean_ctor_get(x_545, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_545, 1);
lean_inc(x_555);
lean_inc(x_1);
lean_inc(x_545);
lean_inc(x_543);
x_556 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_556, 0, x_543);
lean_closure_set(x_556, 1, x_545);
lean_closure_set(x_556, 2, x_1);
x_557 = l_Lean_Meta_getConst_x3f(x_554, x_2, x_3, x_4, x_5, x_553);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
if (lean_obj_tag(x_558) == 0)
{
uint8_t x_559; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_559 = !lean_is_exclusive(x_557);
if (x_559 == 0)
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_ctor_get(x_557, 0);
lean_dec(x_560);
x_561 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_561 == 0)
{
lean_object* x_562; 
x_562 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
lean_ctor_set(x_557, 0, x_562);
return x_557;
}
else
{
lean_dec(x_545);
lean_ctor_set(x_557, 0, x_1);
return x_557;
}
}
else
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_ctor_get(x_557, 1);
lean_inc(x_563);
lean_dec(x_557);
x_564 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; 
x_565 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_563);
return x_566;
}
else
{
lean_object* x_567; 
lean_dec(x_545);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_1);
lean_ctor_set(x_567, 1, x_563);
return x_567;
}
}
}
else
{
lean_object* x_568; 
x_568 = lean_ctor_get(x_558, 0);
lean_inc(x_568);
lean_dec(x_558);
switch (lean_obj_tag(x_568)) {
case 1:
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
lean_dec(x_556);
x_569 = lean_ctor_get(x_557, 1);
lean_inc(x_569);
lean_dec(x_557);
x_570 = l_Lean_ConstantInfo_name(x_568);
x_571 = l_Lean_Meta_isAuxDef(x_570, x_2, x_3, x_4, x_5, x_569);
lean_dec(x_570);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_unbox(x_572);
lean_dec(x_572);
if (x_573 == 0)
{
uint8_t x_574; 
lean_dec(x_568);
lean_dec(x_555);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_574 = !lean_is_exclusive(x_571);
if (x_574 == 0)
{
lean_object* x_575; uint8_t x_576; 
x_575 = lean_ctor_get(x_571, 0);
lean_dec(x_575);
x_576 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_576 == 0)
{
lean_object* x_577; 
x_577 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
lean_ctor_set(x_571, 0, x_577);
return x_571;
}
else
{
lean_dec(x_545);
lean_ctor_set(x_571, 0, x_1);
return x_571;
}
}
else
{
lean_object* x_578; uint8_t x_579; 
x_578 = lean_ctor_get(x_571, 1);
lean_inc(x_578);
lean_dec(x_571);
x_579 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; 
x_580 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_578);
return x_581;
}
else
{
lean_object* x_582; 
lean_dec(x_545);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_1);
lean_ctor_set(x_582, 1, x_578);
return x_582;
}
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_583 = lean_ctor_get(x_571, 1);
lean_inc(x_583);
lean_dec(x_571);
x_584 = lean_unsigned_to_nat(0u);
x_585 = l_Lean_Expr_getAppNumArgsAux(x_1, x_584);
x_586 = lean_mk_empty_array_with_capacity(x_585);
lean_dec(x_585);
lean_inc(x_1);
x_587 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_586);
x_588 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_1, x_543, x_545, x_568, x_555, x_587, x_2, x_3, x_4, x_5, x_583);
lean_dec(x_587);
lean_dec(x_555);
lean_dec(x_568);
lean_dec(x_545);
lean_dec(x_543);
return x_588;
}
}
case 4:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_545);
lean_dec(x_543);
x_589 = lean_ctor_get(x_557, 1);
lean_inc(x_589);
lean_dec(x_557);
x_590 = lean_ctor_get(x_568, 0);
lean_inc(x_590);
lean_dec(x_568);
x_591 = lean_unsigned_to_nat(0u);
x_592 = l_Lean_Expr_getAppNumArgsAux(x_1, x_591);
x_593 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_592);
x_594 = lean_mk_array(x_592, x_593);
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_nat_sub(x_592, x_595);
lean_dec(x_592);
x_597 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_594, x_596);
x_598 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_599 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_590, x_555, x_597, x_556, x_598, x_2, x_3, x_4, x_5, x_589);
lean_dec(x_597);
lean_dec(x_555);
lean_dec(x_590);
return x_599;
}
case 7:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_545);
lean_dec(x_543);
x_600 = lean_ctor_get(x_557, 1);
lean_inc(x_600);
lean_dec(x_557);
x_601 = lean_ctor_get(x_568, 0);
lean_inc(x_601);
lean_dec(x_568);
x_602 = lean_unsigned_to_nat(0u);
x_603 = l_Lean_Expr_getAppNumArgsAux(x_1, x_602);
x_604 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_603);
x_605 = lean_mk_array(x_603, x_604);
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_sub(x_603, x_606);
lean_dec(x_603);
x_608 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_605, x_607);
x_609 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3;
x_610 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_601, x_555, x_608, x_556, x_609, x_2, x_3, x_4, x_5, x_600);
lean_dec(x_608);
lean_dec(x_555);
return x_610;
}
default: 
{
uint8_t x_611; 
lean_dec(x_568);
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_611 = !lean_is_exclusive(x_557);
if (x_611 == 0)
{
lean_object* x_612; uint8_t x_613; 
x_612 = lean_ctor_get(x_557, 0);
lean_dec(x_612);
x_613 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_613 == 0)
{
lean_object* x_614; 
x_614 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
lean_ctor_set(x_557, 0, x_614);
return x_557;
}
else
{
lean_dec(x_545);
lean_ctor_set(x_557, 0, x_1);
return x_557;
}
}
else
{
lean_object* x_615; uint8_t x_616; 
x_615 = lean_ctor_get(x_557, 1);
lean_inc(x_615);
lean_dec(x_557);
x_616 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; 
x_617 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
x_618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_615);
return x_618;
}
else
{
lean_object* x_619; 
lean_dec(x_545);
x_619 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_619, 0, x_1);
lean_ctor_set(x_619, 1, x_615);
return x_619;
}
}
}
}
}
}
else
{
uint8_t x_620; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_620 = !lean_is_exclusive(x_557);
if (x_620 == 0)
{
return x_557;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_557, 0);
x_622 = lean_ctor_get(x_557, 1);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_557);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
return x_623;
}
}
}
else
{
uint8_t x_624; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_624 = !lean_is_exclusive(x_548);
if (x_624 == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = lean_ctor_get(x_548, 0);
lean_dec(x_625);
x_626 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_626 == 0)
{
lean_object* x_627; 
x_627 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
lean_ctor_set(x_548, 0, x_627);
return x_548;
}
else
{
lean_dec(x_545);
lean_ctor_set(x_548, 0, x_1);
return x_548;
}
}
else
{
lean_object* x_628; uint8_t x_629; 
x_628 = lean_ctor_get(x_548, 1);
lean_inc(x_628);
lean_dec(x_548);
x_629 = lean_expr_eqv(x_543, x_545);
lean_dec(x_543);
if (x_629 == 0)
{
lean_object* x_630; lean_object* x_631; 
x_630 = l_Lean_Expr_updateFn(x_1, x_545);
lean_dec(x_545);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_628);
return x_631;
}
else
{
lean_object* x_632; 
lean_dec(x_545);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_1);
lean_ctor_set(x_632, 1, x_628);
return x_632;
}
}
}
}
default: 
{
uint8_t x_633; 
lean_dec(x_549);
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_633 = !lean_is_exclusive(x_548);
if (x_633 == 0)
{
lean_object* x_634; 
x_634 = lean_ctor_get(x_548, 0);
lean_dec(x_634);
lean_ctor_set(x_548, 0, x_1);
return x_548;
}
else
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_548, 1);
lean_inc(x_635);
lean_dec(x_548);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_1);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_548);
if (x_637 == 0)
{
return x_548;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_548, 0);
x_639 = lean_ctor_get(x_548, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_548);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_543);
x_641 = lean_unsigned_to_nat(0u);
x_642 = l_Lean_Expr_getAppNumArgsAux(x_1, x_641);
x_643 = lean_mk_empty_array_with_capacity(x_642);
lean_dec(x_642);
x_644 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_643);
x_645 = l_Lean_Expr_betaRev(x_545, x_644);
lean_dec(x_644);
lean_dec(x_545);
x_1 = x_645;
x_6 = x_546;
goto _start;
}
}
else
{
uint8_t x_647; 
lean_dec(x_543);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_544);
if (x_647 == 0)
{
return x_544;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_544, 0);
x_649 = lean_ctor_get(x_544, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_544);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
case 8:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_1, 2);
lean_inc(x_651);
x_652 = lean_ctor_get(x_1, 3);
lean_inc(x_652);
lean_dec(x_1);
x_653 = lean_expr_instantiate1(x_652, x_651);
lean_dec(x_651);
lean_dec(x_652);
x_1 = x_653;
x_6 = x_540;
goto _start;
}
case 11:
{
lean_object* x_655; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_655 = l_Lean_Meta_reduceProj_x3f(x_1, x_2, x_3, x_4, x_5, x_540);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
if (lean_obj_tag(x_656) == 0)
{
uint8_t x_657; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_657 = !lean_is_exclusive(x_655);
if (x_657 == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_655, 0);
lean_dec(x_658);
lean_ctor_set(x_655, 0, x_1);
return x_655;
}
else
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_655, 1);
lean_inc(x_659);
lean_dec(x_655);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_1);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_1);
x_661 = lean_ctor_get(x_655, 1);
lean_inc(x_661);
lean_dec(x_655);
x_662 = lean_ctor_get(x_656, 0);
lean_inc(x_662);
lean_dec(x_656);
x_1 = x_662;
x_6 = x_661;
goto _start;
}
}
else
{
uint8_t x_664; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_664 = !lean_is_exclusive(x_655);
if (x_664 == 0)
{
return x_655;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_655, 0);
x_666 = lean_ctor_get(x_655, 1);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_655);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
}
default: 
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_1);
x_668 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_669 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2;
x_670 = lean_panic_fn(x_668, x_669);
x_671 = lean_apply_5(x_670, x_2, x_3, x_4, x_5, x_540);
return x_671;
}
}
}
}
default: 
{
lean_object* x_688; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_688, 0, x_1);
lean_ctor_set(x_688, 1, x_6);
return x_688;
}
}
}
}
lean_object* l_Lean_Meta_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinition_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinition_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_3(x_3, x_5, x_6, x_8);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_2, x_10, x_11, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
}
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinition_x3f_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_getStuckMVar_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_16 = l_Lean_Meta_unfoldDefinition_x3f(x_8, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_1 = x_23;
x_6 = x_22;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_8);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_31 = l_Lean_Meta_unfoldDefinition_x3f(x_8, x_2, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_1 = x_37;
x_6 = x_36;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
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
else
{
lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_Meta_synthPending(x_45, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
lean_ctor_set(x_46, 0, x_8);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_8);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_1 = x_8;
x_6 = x_53;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_10);
if (x_59 == 0)
{
return x_10;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_ConstantInfo_lparams(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_List_lengthAux___rarg(x_8, x_9);
lean_dec(x_8);
x_11 = l_List_lengthAux___rarg(x_2, x_9);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_instantiate_value_lparams(x_1, x_2);
x_16 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_lparams(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___rarg(x_2, x_10);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_instantiate_value_lparams(x_1, x_2);
x_17 = l_Lean_Expr_betaRev(x_16, x_3);
lean_dec(x_16);
x_18 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_lparams(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___rarg(x_2, x_10);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_instantiate_value_lparams(x_1, x_2);
x_17 = l_Lean_Expr_betaRev(x_16, x_3);
lean_dec(x_16);
x_18 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_17);
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfUntilIdRhs(x_18, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_21);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
uint8_t x_34; 
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
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_getConstNoEx_x3f(x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_17; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_17, x_8, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l_Lean_Expr_getAppFn(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_getConst_x3f(x_28, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
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
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_30, 1);
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = l_Lean_ConstantInfo_lparams(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_List_lengthAux___rarg(x_42, x_43);
lean_dec(x_42);
x_45 = l_List_lengthAux___rarg(x_29, x_43);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
lean_ctor_set(x_30, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_30, 0, x_51);
return x_30;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_30);
x_52 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_53 = lean_mk_empty_array_with_capacity(x_52);
lean_dec(x_52);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_53);
x_55 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_41, x_29, x_54, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_54);
lean_dec(x_29);
lean_dec(x_41);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_30);
x_56 = l_Lean_ConstantInfo_name(x_41);
x_57 = l_Lean_Meta_smartUnfoldingSuffix;
x_58 = lean_name_mk_string(x_56, x_57);
x_59 = l_Lean_Meta_getConstNoEx_x3f(x_58, x_2, x_3, x_4, x_5, x_39);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_59, 0);
lean_dec(x_63);
x_64 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
lean_ctor_set(x_59, 0, x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_59);
x_66 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_67);
x_69 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_41, x_29, x_68, x_2, x_3, x_4, x_5, x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_68);
lean_dec(x_29);
lean_dec(x_41);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_75 = lean_mk_empty_array_with_capacity(x_74);
lean_dec(x_74);
x_76 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_75);
x_77 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_41, x_29, x_76, x_2, x_3, x_4, x_5, x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_76);
lean_dec(x_29);
lean_dec(x_41);
return x_77;
}
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_60, 0);
lean_inc(x_78);
lean_dec(x_60);
if (lean_obj_tag(x_78) == 1)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_41);
x_79 = lean_ctor_get(x_59, 1);
lean_inc(x_79);
lean_dec(x_59);
x_80 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_81 = lean_mk_empty_array_with_capacity(x_80);
lean_dec(x_80);
x_82 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_81);
x_83 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(x_78, x_29, x_82, x_2, x_3, x_4, x_5, x_79);
lean_dec(x_82);
lean_dec(x_29);
lean_dec(x_78);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_59);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_59, 1);
x_86 = lean_ctor_get(x_59, 0);
lean_dec(x_86);
x_87 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_box(0);
lean_ctor_set(x_59, 0, x_88);
return x_59;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_59);
x_89 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_90 = lean_mk_empty_array_with_capacity(x_89);
lean_dec(x_89);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_90);
x_92 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_41, x_29, x_91, x_2, x_3, x_4, x_5, x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_91);
lean_dec(x_29);
lean_dec(x_41);
return x_92;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_59, 1);
lean_inc(x_93);
lean_dec(x_59);
x_94 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_98 = lean_mk_empty_array_with_capacity(x_97);
lean_dec(x_97);
x_99 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_98);
x_100 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_41, x_29, x_99, x_2, x_3, x_4, x_5, x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_99);
lean_dec(x_29);
lean_dec(x_41);
return x_100;
}
}
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_101 = lean_ctor_get(x_30, 1);
lean_inc(x_101);
lean_dec(x_30);
x_102 = lean_ctor_get(x_31, 0);
lean_inc(x_102);
lean_dec(x_31);
x_103 = l_Lean_ConstantInfo_lparams(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_List_lengthAux___rarg(x_103, x_104);
lean_dec(x_103);
x_106 = l_List_lengthAux___rarg(x_29, x_104);
x_107 = lean_nat_dec_eq(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_102);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_101);
return x_109;
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_4, 0);
lean_inc(x_110);
x_111 = l___private_Lean_Meta_WHNF_0__Lean_Meta_useSmartUnfolding(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_ConstantInfo_hasValue(x_102);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_102);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_101);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = l_Lean_Expr_getAppNumArgsAux(x_1, x_104);
x_116 = lean_mk_empty_array_with_capacity(x_115);
lean_dec(x_115);
x_117 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_116);
x_118 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_102, x_29, x_117, x_2, x_3, x_4, x_5, x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_117);
lean_dec(x_29);
lean_dec(x_102);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = l_Lean_ConstantInfo_name(x_102);
x_120 = l_Lean_Meta_smartUnfoldingSuffix;
x_121 = lean_name_mk_string(x_119, x_120);
x_122 = l_Lean_Meta_getConstNoEx_x3f(x_121, x_2, x_3, x_4, x_5, x_101);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
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
x_126 = l_Lean_ConstantInfo_hasValue(x_102);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_102);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_124);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_125);
x_129 = l_Lean_Expr_getAppNumArgsAux(x_1, x_104);
x_130 = lean_mk_empty_array_with_capacity(x_129);
lean_dec(x_129);
x_131 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_130);
x_132 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_102, x_29, x_131, x_2, x_3, x_4, x_5, x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_131);
lean_dec(x_29);
lean_dec(x_102);
return x_132;
}
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
lean_dec(x_123);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_102);
x_134 = lean_ctor_get(x_122, 1);
lean_inc(x_134);
lean_dec(x_122);
x_135 = l_Lean_Expr_getAppNumArgsAux(x_1, x_104);
x_136 = lean_mk_empty_array_with_capacity(x_135);
lean_dec(x_135);
x_137 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_136);
x_138 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3(x_133, x_29, x_137, x_2, x_3, x_4, x_5, x_134);
lean_dec(x_137);
lean_dec(x_29);
lean_dec(x_133);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_133);
x_139 = lean_ctor_get(x_122, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_140 = x_122;
} else {
 lean_dec_ref(x_122);
 x_140 = lean_box(0);
}
x_141 = l_Lean_ConstantInfo_hasValue(x_102);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_102);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_140);
x_144 = l_Lean_Expr_getAppNumArgsAux(x_1, x_104);
x_145 = lean_mk_empty_array_with_capacity(x_144);
lean_dec(x_144);
x_146 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_145);
x_147 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2(x_102, x_29, x_146, x_2, x_3, x_4, x_5, x_139);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_146);
lean_dec(x_29);
lean_dec(x_102);
return x_147;
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
uint8_t x_148; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_30);
if (x_148 == 0)
{
return x_30;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_30, 0);
x_150 = lean_ctor_get(x_30, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_30);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_6);
return x_153;
}
}
default: 
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_6);
return x_155;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at_Lean_Meta_unfoldDefinition_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_whnfHeadPred_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfHeadPred_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfHeadPred___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_whnfHeadPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
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
x_37 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_35, x_12, x_36);
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
x_46 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_43, x_12, x_45);
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
x_71 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_67, x_12, x_70);
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
x_95 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_133 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_171 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_211 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPred___at_Lean_Meta_whnfUntil___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_4, x_1, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 7:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_36);
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
x_56 = l_Lean_Expr_getAppArgs___closed__1;
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
x_68 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_67);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_67, x_70);
lean_dec(x_67);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_69, x_71);
x_73 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_74 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_75 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_65, x_25, x_72, x_73, x_74, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_72);
lean_dec(x_25);
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
lean_dec(x_99);
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
x_117 = l_Lean_Expr_getAppArgs___closed__1;
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
x_129 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_128);
x_130 = lean_mk_array(x_128, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_128, x_131);
lean_dec(x_128);
x_133 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_130, x_132);
x_134 = l_Lean_Meta_reduceRecMatcher_x3f___closed__1;
x_135 = l_Lean_Meta_reduceRecMatcher_x3f___closed__2;
x_136 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_126, x_90, x_133, x_134, x_135, x_2, x_3, x_4, x_5, x_125);
lean_dec(x_133);
lean_dec(x_90);
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
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceRecMatcher_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceRecMatcher_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Lean_Environment_evalConstCheck___rarg(x_11, x_12, x_1, x_2);
x_14 = l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_13);
return x_14;
}
}
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_instQuoteBool___closed__2;
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_reduceBoolNativeUnsafe___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Literal_type___closed__2;
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Meta_reduceBoolNative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_reduceBoolNative___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Meta_reduceNatNative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNatNative___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Meta_reduceNative_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
uint64_t x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_13 = lean_box_uint64(x_9);
x_14 = lean_box_uint64(x_12);
x_15 = lean_box_uint64(x_6);
x_16 = lean_apply_7(x_2, x_7, x_8, x_13, x_10, x_11, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_apply_1(x_3, x_1);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_apply_1(x_3, x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_apply_1(x_3, x_1);
return x_19;
}
}
}
lean_object* l_Lean_Meta_reduceNative_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNative_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBool");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceNat");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToExprBool___lambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToExprBool___lambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_12 = lean_name_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_reduceNative_x3f___closed__4;
x_14 = lean_name_eq(x_9, x_13);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
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
x_36 = l_Lean_Meta_reduceNative_x3f___closed__5;
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Meta_reduceNative_x3f___closed__5;
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
x_42 = l_Lean_Meta_reduceNative_x3f___closed__6;
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_withNatValue_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
uint64_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get_usize(x_5, 2);
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get_usize(x_6, 2);
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = l_Lean_Literal_type___closed__1;
x_19 = lean_string_dec_eq(x_15, x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_20 = lean_apply_1(x_4, x_1);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_25 = lean_string_dec_eq(x_11, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_18);
x_26 = lean_apply_1(x_4, x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_27 = lean_box_uint64(x_10);
x_28 = lean_box_usize(x_16);
x_29 = lean_box_usize(x_12);
x_30 = lean_apply_4(x_2, x_8, x_27, x_28, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_1);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_32 = lean_string_dec_eq(x_11, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_18);
x_33 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_10);
x_34 = lean_apply_1(x_4, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_35 = lean_box_uint64(x_10);
x_36 = lean_box_usize(x_16);
x_37 = lean_box_usize(x_12);
x_38 = lean_apply_4(x_2, x_8, x_35, x_36, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_39);
lean_dec(x_6);
x_41 = l_Lean_Literal_type___closed__1;
x_42 = lean_string_dec_eq(x_39, x_41);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_43 = lean_apply_1(x_4, x_1);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_44 = x_1;
} else {
 lean_dec_ref(x_1);
 x_44 = lean_box(0);
}
x_45 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_46 = lean_string_dec_eq(x_11, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_47, 0, x_7);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set_usize(x_47, 2, x_40);
lean_ctor_set(x_5, 0, x_47);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(4, 2, 8);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set_uint64(x_48, sizeof(void*)*2, x_10);
x_49 = lean_apply_1(x_4, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_50 = lean_box_uint64(x_10);
x_51 = lean_box_usize(x_40);
x_52 = lean_box_usize(x_12);
x_53 = lean_apply_4(x_2, x_8, x_50, x_51, x_52);
return x_53;
}
}
}
}
else
{
uint64_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_55 = lean_ctor_get(x_5, 1);
x_56 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
x_58 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_59 = x_6;
} else {
 lean_dec_ref(x_6);
 x_59 = lean_box(0);
}
x_60 = l_Lean_Literal_type___closed__1;
x_61 = lean_string_dec_eq(x_57, x_60);
lean_dec(x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_2);
x_62 = lean_apply_1(x_4, x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_63 = x_1;
} else {
 lean_dec_ref(x_1);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_65 = lean_string_dec_eq(x_55, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_66 = x_59;
}
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set_usize(x_66, 2, x_58);
x_67 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
lean_ctor_set_usize(x_67, 2, x_56);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(4, 2, 8);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
lean_ctor_set_uint64(x_68, sizeof(void*)*2, x_54);
x_69 = lean_apply_1(x_4, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_4);
x_70 = lean_box_uint64(x_54);
x_71 = lean_box_usize(x_58);
x_72 = lean_box_usize(x_56);
x_73 = lean_apply_4(x_2, x_8, x_70, x_71, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_74 = lean_apply_1(x_4, x_1);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_75 = lean_apply_1(x_4, x_1);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_5);
lean_dec(x_2);
x_76 = lean_apply_1(x_4, x_1);
return x_76;
}
}
case 9:
{
lean_object* x_77; 
lean_dec(x_2);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_78 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_box_uint64(x_78);
x_81 = lean_apply_2(x_3, x_79, x_80);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_3);
x_82 = lean_apply_1(x_4, x_1);
return x_82;
}
}
default: 
{
lean_object* x_83; 
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_apply_1(x_4, x_1);
return x_83;
}
}
}
}
lean_object* l_Lean_Meta_withNatValue_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNatValue_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_18 = l_Lean_Literal_type___closed__1;
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
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_29 = l_Lean_Literal_type___closed__1;
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
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
lean_object* l_Lean_Meta_withNatValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNatValue___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_17 = l_Lean_Literal_type___closed__1;
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
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_25 = l_Lean_mkNatLit(x_24);
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
x_30 = l_Lean_Literal_type___closed__1;
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
x_34 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_40 = l_Lean_mkNatLit(x_39);
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
x_66 = l_Lean_mkNatLit(x_65);
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
x_71 = l_Lean_mkNatLit(x_70);
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
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isExprDefEq___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBinOp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__1;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_KernelException_toMessageData___closed__15;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" op ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__6;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__10;
x_2 = l_Lean_KernelException_toMessageData___closed__15;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_reduceBinNatOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_19 = l_Lean_Literal_type___closed__1;
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
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_25 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_15);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_31 = x_25;
} else {
 lean_dec_ref(x_25);
 x_31 = lean_box(0);
}
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
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_string_dec_eq(x_32, x_22);
lean_dec(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_31;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_st_ref_get(x_7, x_30);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = 0;
x_40 = x_68;
x_41 = x_67;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_71 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_70, x_4, x_5, x_6, x_7, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
x_40 = x_74;
x_41 = x_73;
goto block_62;
}
block_62:
{
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_apply_2(x_1, x_42, x_42);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_31)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_31;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_31);
x_47 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_48 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_49 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_47, x_48, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_apply_2(x_1, x_52, x_52);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_apply_2(x_1, x_57, x_57);
x_59 = l_Lean_mkNatLit(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_25);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_25, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_25, 0, x_77);
return x_25;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_dec(x_25);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_25);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_25, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_25, 0, x_83);
return x_25;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_25, 1);
lean_inc(x_84);
lean_dec(x_25);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_25);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_25, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_25, 0, x_89);
return x_25;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_25, 1);
lean_inc(x_90);
lean_dec(x_25);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
case 9:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_26, 0);
lean_inc(x_93);
lean_dec(x_26);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_94 = lean_ctor_get(x_25, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_95 = x_25;
} else {
 lean_dec_ref(x_25);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_125 = lean_st_ref_get(x_7, x_94);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 3);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_ctor_get_uint8(x_127, sizeof(void*)*1);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = 0;
x_97 = x_130;
x_98 = x_129;
goto block_124;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_dec(x_125);
x_132 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_133 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_132, x_4, x_5, x_6, x_7, x_131);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_97 = x_136;
x_98 = x_135;
goto block_124;
}
block_124:
{
if (x_97 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_apply_2(x_1, x_99, x_96);
x_101 = l_Lean_mkNatLit(x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_95);
lean_inc(x_96);
x_104 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_96);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_KernelException_toMessageData___closed__15;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_111 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_110, x_109, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_apply_2(x_1, x_114, x_96);
x_116 = l_Lean_mkNatLit(x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_111, 0, x_117);
return x_111;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_dec(x_111);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_apply_2(x_1, x_119, x_96);
x_121 = l_Lean_mkNatLit(x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_25);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_25, 0);
lean_dec(x_138);
x_139 = lean_box(0);
lean_ctor_set(x_25, 0, x_139);
return x_25;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_25, 1);
lean_inc(x_140);
lean_dec(x_25);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
default: 
{
uint8_t x_143; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_25);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_25, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_25, 0, x_145);
return x_25;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_25, 1);
lean_inc(x_146);
lean_dec(x_25);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_25);
if (x_149 == 0)
{
return x_25;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_25, 0);
x_151 = lean_ctor_get(x_25, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_25);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_9, 1);
lean_inc(x_153);
lean_dec(x_9);
x_154 = lean_ctor_get(x_11, 1);
lean_inc(x_154);
lean_dec(x_11);
x_155 = lean_ctor_get(x_12, 1);
lean_inc(x_155);
lean_dec(x_12);
x_156 = l_Lean_Literal_type___closed__1;
x_157 = lean_string_dec_eq(x_155, x_156);
lean_dec(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_154);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_153);
return x_159;
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_161 = lean_string_dec_eq(x_154, x_160);
lean_dec(x_154);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_153);
return x_163;
}
else
{
lean_object* x_164; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_164 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_153);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
switch (lean_obj_tag(x_165)) {
case 4:
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 1)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
lean_dec(x_167);
x_173 = lean_string_dec_eq(x_172, x_156);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_174 = lean_box(0);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
return x_175;
}
else
{
uint8_t x_176; 
x_176 = lean_string_dec_eq(x_171, x_160);
lean_dec(x_171);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_177 = lean_box(0);
if (lean_is_scalar(x_170)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_170;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_169);
return x_178;
}
else
{
uint8_t x_179; lean_object* x_180; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_st_ref_get(x_7, x_169);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 3);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_ctor_get_uint8(x_199, sizeof(void*)*1);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
lean_dec(x_197);
x_202 = 0;
x_179 = x_202;
x_180 = x_201;
goto block_196;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
lean_dec(x_197);
x_204 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_205 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_204, x_4, x_5, x_6, x_7, x_203);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_unbox(x_206);
lean_dec(x_206);
x_179 = x_208;
x_180 = x_207;
goto block_196;
}
block_196:
{
if (x_179 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_apply_2(x_1, x_181, x_181);
x_183 = l_Lean_mkNatLit(x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
if (lean_is_scalar(x_170)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_170;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_170);
x_186 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_187 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_188 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_186, x_187, x_4, x_5, x_6, x_7, x_180);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
x_191 = lean_unsigned_to_nat(0u);
x_192 = lean_apply_2(x_1, x_191, x_191);
x_193 = l_Lean_mkNatLit(x_192);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_190;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_189);
return x_195;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_209 = lean_ctor_get(x_164, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_210 = x_164;
} else {
 lean_dec_ref(x_164);
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
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_213 = lean_ctor_get(x_164, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_214 = x_164;
} else {
 lean_dec_ref(x_164);
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
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_166);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_217 = lean_ctor_get(x_164, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_218 = x_164;
} else {
 lean_dec_ref(x_164);
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
case 9:
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_165, 0);
lean_inc(x_221);
lean_dec(x_165);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_222 = lean_ctor_get(x_164, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_223 = x_164;
} else {
 lean_dec_ref(x_164);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
x_248 = lean_st_ref_get(x_7, x_222);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 3);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_ctor_get_uint8(x_250, sizeof(void*)*1);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_248, 1);
lean_inc(x_252);
lean_dec(x_248);
x_253 = 0;
x_225 = x_253;
x_226 = x_252;
goto block_247;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_254 = lean_ctor_get(x_248, 1);
lean_inc(x_254);
lean_dec(x_248);
x_255 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_256 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_255, x_4, x_5, x_6, x_7, x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_unbox(x_257);
lean_dec(x_257);
x_225 = x_259;
x_226 = x_258;
goto block_247;
}
block_247:
{
if (x_225 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_227 = lean_unsigned_to_nat(0u);
x_228 = lean_apply_2(x_1, x_227, x_224);
x_229 = l_Lean_mkNatLit(x_228);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
if (lean_is_scalar(x_223)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_223;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_223);
lean_inc(x_224);
x_232 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_224);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_KernelException_toMessageData___closed__15;
x_237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_239 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_238, x_237, x_4, x_5, x_6, x_7, x_226);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
x_242 = lean_unsigned_to_nat(0u);
x_243 = lean_apply_2(x_1, x_242, x_224);
x_244 = l_Lean_mkNatLit(x_243);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
if (lean_is_scalar(x_241)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_241;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_240);
return x_246;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_221);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_260 = lean_ctor_get(x_164, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_261 = x_164;
} else {
 lean_dec_ref(x_164);
 x_261 = lean_box(0);
}
x_262 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_264 = lean_ctor_get(x_164, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_265 = x_164;
} else {
 lean_dec_ref(x_164);
 x_265 = lean_box(0);
}
x_266 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_268 = lean_ctor_get(x_164, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_164, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_270 = x_164;
} else {
 lean_dec_ref(x_164);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_13);
lean_dec(x_12);
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
else
{
uint8_t x_278; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_9);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_9, 0);
lean_dec(x_279);
x_280 = lean_box(0);
lean_ctor_set(x_9, 0, x_280);
return x_9;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_9, 1);
lean_inc(x_281);
lean_dec(x_9);
x_282 = lean_box(0);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_9);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_9, 0);
lean_dec(x_285);
x_286 = lean_box(0);
lean_ctor_set(x_9, 0, x_286);
return x_9;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_9, 1);
lean_inc(x_287);
lean_dec(x_9);
x_288 = lean_box(0);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
}
case 9:
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_10, 0);
lean_inc(x_290);
lean_dec(x_10);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_9, 1);
lean_inc(x_291);
lean_dec(x_9);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_293 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_291);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
switch (lean_obj_tag(x_294)) {
case 4:
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec(x_294);
if (lean_obj_tag(x_295) == 1)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 1)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_299 = x_293;
} else {
 lean_dec_ref(x_293);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_295, 1);
lean_inc(x_300);
lean_dec(x_295);
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
lean_dec(x_296);
x_302 = l_Lean_Literal_type___closed__1;
x_303 = lean_string_dec_eq(x_301, x_302);
lean_dec(x_301);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_300);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_304 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_299;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_298);
return x_305;
}
else
{
lean_object* x_306; uint8_t x_307; 
x_306 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
x_307 = lean_string_dec_eq(x_300, x_306);
lean_dec(x_300);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_308 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_299;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_298);
return x_309;
}
else
{
uint8_t x_310; lean_object* x_311; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_341 = lean_st_ref_get(x_7, x_298);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 3);
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_ctor_get_uint8(x_343, sizeof(void*)*1);
lean_dec(x_343);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_341, 1);
lean_inc(x_345);
lean_dec(x_341);
x_346 = 0;
x_310 = x_346;
x_311 = x_345;
goto block_340;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_347 = lean_ctor_get(x_341, 1);
lean_inc(x_347);
lean_dec(x_341);
x_348 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_349 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_348, x_4, x_5, x_6, x_7, x_347);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_unbox(x_350);
lean_dec(x_350);
x_310 = x_352;
x_311 = x_351;
goto block_340;
}
block_340:
{
if (x_310 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_312 = lean_unsigned_to_nat(0u);
x_313 = lean_apply_2(x_1, x_292, x_312);
x_314 = l_Lean_mkNatLit(x_313);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_314);
if (lean_is_scalar(x_299)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_299;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_311);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
lean_dec(x_299);
lean_inc(x_292);
x_317 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_292);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Lean_KernelException_toMessageData___closed__15;
x_320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_324 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_319);
x_326 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_327 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_326, x_325, x_4, x_5, x_6, x_7, x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_327, 0);
lean_dec(x_329);
x_330 = lean_unsigned_to_nat(0u);
x_331 = lean_apply_2(x_1, x_292, x_330);
x_332 = l_Lean_mkNatLit(x_331);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_327, 0, x_333);
return x_327;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_334 = lean_ctor_get(x_327, 1);
lean_inc(x_334);
lean_dec(x_327);
x_335 = lean_unsigned_to_nat(0u);
x_336 = lean_apply_2(x_1, x_292, x_335);
x_337 = l_Lean_mkNatLit(x_336);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_334);
return x_339;
}
}
}
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_353 = !lean_is_exclusive(x_293);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_293, 0);
lean_dec(x_354);
x_355 = lean_box(0);
lean_ctor_set(x_293, 0, x_355);
return x_293;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_293, 1);
lean_inc(x_356);
lean_dec(x_293);
x_357 = lean_box(0);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_359 = !lean_is_exclusive(x_293);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_293, 0);
lean_dec(x_360);
x_361 = lean_box(0);
lean_ctor_set(x_293, 0, x_361);
return x_293;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_293, 1);
lean_inc(x_362);
lean_dec(x_293);
x_363 = lean_box(0);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_295);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_293);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_293, 0);
lean_dec(x_366);
x_367 = lean_box(0);
lean_ctor_set(x_293, 0, x_367);
return x_293;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_293, 1);
lean_inc(x_368);
lean_dec(x_293);
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
case 9:
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_294, 0);
lean_inc(x_371);
lean_dec(x_294);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_372 = lean_ctor_get(x_293, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_373 = x_293;
} else {
 lean_dec_ref(x_293);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_371, 0);
lean_inc(x_374);
lean_dec(x_371);
x_404 = lean_st_ref_get(x_7, x_372);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_405, 3);
lean_inc(x_406);
lean_dec(x_405);
x_407 = lean_ctor_get_uint8(x_406, sizeof(void*)*1);
lean_dec(x_406);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
lean_dec(x_404);
x_409 = 0;
x_375 = x_409;
x_376 = x_408;
goto block_403;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_410 = lean_ctor_get(x_404, 1);
lean_inc(x_410);
lean_dec(x_404);
x_411 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_412 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_411, x_4, x_5, x_6, x_7, x_410);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_unbox(x_413);
lean_dec(x_413);
x_375 = x_415;
x_376 = x_414;
goto block_403;
}
block_403:
{
if (x_375 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_377 = lean_apply_2(x_1, x_292, x_374);
x_378 = l_Lean_mkNatLit(x_377);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_378);
if (lean_is_scalar(x_373)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_373;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_376);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_373);
lean_inc(x_292);
x_381 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_292);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = l_Lean_KernelException_toMessageData___closed__15;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
lean_inc(x_374);
x_387 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_374);
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_387);
x_389 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_383);
x_391 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_392 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_391, x_390, x_4, x_5, x_6, x_7, x_376);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_392, 0);
lean_dec(x_394);
x_395 = lean_apply_2(x_1, x_292, x_374);
x_396 = l_Lean_mkNatLit(x_395);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_392, 0, x_397);
return x_392;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_398 = lean_ctor_get(x_392, 1);
lean_inc(x_398);
lean_dec(x_392);
x_399 = lean_apply_2(x_1, x_292, x_374);
x_400 = l_Lean_mkNatLit(x_399);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_398);
return x_402;
}
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_371);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_416 = !lean_is_exclusive(x_293);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_293, 0);
lean_dec(x_417);
x_418 = lean_box(0);
lean_ctor_set(x_293, 0, x_418);
return x_293;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_293, 1);
lean_inc(x_419);
lean_dec(x_293);
x_420 = lean_box(0);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
default: 
{
uint8_t x_422; 
lean_dec(x_294);
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_293);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_293, 0);
lean_dec(x_423);
x_424 = lean_box(0);
lean_ctor_set(x_293, 0, x_424);
return x_293;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_293, 1);
lean_inc(x_425);
lean_dec(x_293);
x_426 = lean_box(0);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
}
}
else
{
uint8_t x_428; 
lean_dec(x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_428 = !lean_is_exclusive(x_293);
if (x_428 == 0)
{
return x_293;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_293, 0);
x_430 = lean_ctor_get(x_293, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_293);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
uint8_t x_432; 
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_432 = !lean_is_exclusive(x_9);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_9, 0);
lean_dec(x_433);
x_434 = lean_box(0);
lean_ctor_set(x_9, 0, x_434);
return x_9;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_9, 1);
lean_inc(x_435);
lean_dec(x_9);
x_436 = lean_box(0);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
}
default: 
{
uint8_t x_438; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_438 = !lean_is_exclusive(x_9);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_9, 0);
lean_dec(x_439);
x_440 = lean_box(0);
lean_ctor_set(x_9, 0, x_440);
return x_9;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_9, 1);
lean_inc(x_441);
lean_dec(x_9);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_9);
if (x_444 == 0)
{
return x_9;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_9, 0);
x_446 = lean_ctor_get(x_9, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_9);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
lean_object* l_Lean_Meta_reduceBinNatPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_19 = l_Lean_Literal_type___closed__1;
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
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_25 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_15);
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
x_41 = l_Lean_Meta_reduceNative_x3f___closed__5;
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_55 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_84 = l_Lean_Meta_reduceNative_x3f___closed__5;
lean_ctor_set(x_25, 0, x_84);
return x_25;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_91 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_114 = l_Lean_Literal_type___closed__1;
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
x_118 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_122 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_111);
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
x_140 = l_Lean_Meta_reduceNative_x3f___closed__5;
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
x_142 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_163 = l_Lean_Meta_reduceNative_x3f___closed__5;
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
x_165 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_200 = l_Lean_Meta_whnf(x_3, x_4, x_5, x_6, x_7, x_198);
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
x_209 = l_Lean_Literal_type___closed__1;
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
x_212 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_218 = l_Lean_Meta_reduceNative_x3f___closed__5;
lean_ctor_set(x_200, 0, x_218);
return x_200;
}
else
{
lean_object* x_219; 
x_219 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_223 = l_Lean_Literal_type___closed__1;
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
x_227 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__1;
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
x_234 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_220);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_262 = l_Lean_Meta_reduceNative_x3f___closed__5;
lean_ctor_set(x_200, 0, x_262);
return x_200;
}
else
{
lean_object* x_263; 
x_263 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
x_268 = l_Lean_Meta_reduceNative_x3f___closed__5;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_264);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = l_Lean_Meta_reduceNative_x3f___closed__6;
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
lean_object* l_Lean_Meta_reduceNat_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 4:
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_11 = lean_box_uint64(x_10);
x_12 = lean_box_uint64(x_7);
x_13 = lean_apply_5(x_2, x_8, x_9, x_11, x_6, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_14, sizeof(void*)*2);
lean_dec(x_14);
x_22 = lean_box_uint64(x_21);
x_23 = lean_box_uint64(x_18);
x_24 = lean_box_uint64(x_16);
x_25 = lean_apply_7(x_3, x_19, x_20, x_22, x_17, x_23, x_15, x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_apply_1(x_4, x_1);
return x_26;
}
}
default: 
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_apply_1(x_4, x_1);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_apply_1(x_4, x_1);
return x_28;
}
}
}
lean_object* l_Lean_Meta_reduceNat_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNat_x3f_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object* x_1) {
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
x_1 = l_Lean_Literal_type___closed__2;
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
x_1 = l_Lean_Literal_type___closed__2;
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
x_1 = l_Lean_Literal_type___closed__2;
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
x_1 = l_Lean_Literal_type___closed__2;
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
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_myMacro____x40_Init_Notation___hyg_6227____closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ble");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_ble___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_reduceNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___closed__4;
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
x_32 = l_Lean_Meta_reduceNat_x3f___closed__12;
x_33 = lean_name_eq(x_21, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_reduceNat_x3f___closed__14;
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
x_38 = l_Lean_Meta_reduceNat_x3f___closed__15;
x_39 = l_Lean_Meta_reduceBinNatPred(x_38, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_40 = l_Lean_Meta_reduceNat_x3f___closed__16;
x_41 = l_Lean_Meta_reduceBinNatPred(x_40, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_21);
x_42 = l_Nat_instModNat___closed__1;
x_43 = l_Lean_Meta_reduceBinNatOp(x_42, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_21);
x_44 = l_Nat_instDivNat___closed__1;
x_45 = l_Lean_Meta_reduceBinNatOp(x_44, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = l_instMulNat___closed__1;
x_47 = l_Lean_Meta_reduceBinNatOp(x_46, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
x_48 = l_instSubNat___closed__1;
x_49 = l_Lean_Meta_reduceBinNatOp(x_48, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_21);
x_50 = l_instAddNat___closed__1;
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
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_reduceNat_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_9, 5);
x_11 = 2;
x_12 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
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
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
x_3 = lean_unsigned_to_nat(502u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, 5);
lean_dec(x_13);
x_15 = lean_box(x_14);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_19, x_2);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 4);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_24, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
case 1:
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_30, x_2);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_35, x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
x_39 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_40 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_41 = lean_panic_fn(x_39, x_40);
x_42 = lean_apply_5(x_41, x_3, x_4, x_5, x_6, x_38);
return x_42;
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
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
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
x_3 = lean_unsigned_to_nat(512u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, 5);
lean_dec(x_10);
x_12 = lean_box(x_11);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_st_ref_get(x_7, x_8);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_17, 4);
lean_inc(x_3);
x_23 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_22, x_2, x_3);
lean_ctor_set(x_17, 4, x_23);
x_24 = lean_st_ref_set(x_5, x_16, x_18);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_3);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get(x_17, 3);
x_33 = lean_ctor_get(x_17, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_3);
x_34 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_33, x_2, x_3);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_16, 1, x_35);
x_36 = lean_st_ref_set(x_5, x_16, x_18);
lean_dec(x_5);
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
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 2);
x_42 = lean_ctor_get(x_16, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_17, 4);
lean_inc(x_47);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 x_48 = x_17;
} else {
 lean_dec_ref(x_17);
 x_48 = lean_box(0);
}
lean_inc(x_3);
x_49 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_47, x_2, x_3);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 5, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_45);
lean_ctor_set(x_50, 3, x_46);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
x_52 = lean_st_ref_set(x_5, x_51, x_18);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
case 1:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_6);
lean_dec(x_4);
x_56 = lean_st_ref_get(x_7, x_8);
lean_dec(x_7);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_take(x_5, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_60, 3);
lean_inc(x_3);
x_66 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_65, x_2, x_3);
lean_ctor_set(x_60, 3, x_66);
x_67 = lean_st_ref_set(x_5, x_59, x_61);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_3);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_60, 0);
x_73 = lean_ctor_get(x_60, 1);
x_74 = lean_ctor_get(x_60, 2);
x_75 = lean_ctor_get(x_60, 4);
x_76 = lean_ctor_get(x_60, 3);
lean_inc(x_75);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_60);
lean_inc(x_3);
x_77 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_76, x_2, x_3);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_75);
lean_ctor_set(x_59, 1, x_78);
x_79 = lean_st_ref_set(x_5, x_59, x_61);
lean_dec(x_5);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_83 = lean_ctor_get(x_59, 0);
x_84 = lean_ctor_get(x_59, 2);
x_85 = lean_ctor_get(x_59, 3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_59);
x_86 = lean_ctor_get(x_60, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_60, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_60, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_60, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_60, 3);
lean_inc(x_90);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_91 = x_60;
} else {
 lean_dec_ref(x_60);
 x_91 = lean_box(0);
}
lean_inc(x_3);
x_92 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_90, x_2, x_3);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_89);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_84);
lean_ctor_set(x_94, 3, x_85);
x_95 = lean_st_ref_set(x_5, x_94, x_61);
lean_dec(x_5);
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
lean_ctor_set(x_98, 0, x_3);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_12);
lean_dec(x_2);
x_99 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_100 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
x_101 = lean_panic_fn(x_99, x_100);
x_102 = lean_apply_5(x_101, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_3);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_3);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_102);
if (x_107 == 0)
{
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_whnfImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfImp_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfImp_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfImp_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfImp_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
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
x_36 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_34, x_11, x_35);
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
x_45 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_42, x_11, x_44);
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
x_70 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_66, x_11, x_69);
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
uint8_t x_94; lean_object* x_95; uint8_t x_168; 
x_168 = l_Lean_Expr_hasFVar(x_1);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Expr_hasExprMVar(x_1);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_2, 0);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, 5);
lean_dec(x_170);
x_172 = 2;
x_173 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_171, x_172);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = 1;
x_94 = x_174;
x_95 = x_6;
goto block_167;
}
else
{
uint8_t x_175; 
x_175 = 0;
x_94 = x_175;
x_95 = x_6;
goto block_167;
}
}
else
{
uint8_t x_176; 
x_176 = 0;
x_94 = x_176;
x_95 = x_6;
goto block_167;
}
}
else
{
uint8_t x_177; 
x_177 = 0;
x_94 = x_177;
x_95 = x_6;
goto block_167;
}
block_167:
{
lean_object* x_96; lean_object* x_97; 
if (x_94 == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_96 = x_139;
x_97 = x_95;
goto block_138;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_140 = lean_st_ref_get(x_5, x_95);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_get(x_3, x_141);
x_143 = lean_ctor_get(x_2, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_143, 5);
lean_dec(x_143);
x_145 = lean_box(x_144);
switch (lean_obj_tag(x_145)) {
case 0:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_148, 4);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_149, x_1);
x_96 = x_150;
x_97 = x_147;
goto block_138;
}
case 1:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_142, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_dec(x_142);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_153, 3);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_154, x_1);
x_96 = x_155;
x_97 = x_152;
goto block_138;
}
default: 
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_145);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_dec(x_142);
x_157 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_158 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_159 = lean_panic_fn(x_157, x_158);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_160 = lean_apply_5(x_159, x_2, x_3, x_4, x_5, x_156);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_96 = x_161;
x_97 = x_162;
goto block_138;
}
else
{
uint8_t x_163; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 0);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_160);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
}
block_138:
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_98; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_98 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_99);
x_101 = l_Lean_Meta_reduceNat_x3f(x_99, x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_99);
x_104 = l_Lean_Meta_reduceNative_x3f(x_99, x_2, x_3, x_4, x_5, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_99);
x_107 = l_Lean_Meta_unfoldDefinition_x3f(x_99, x_2, x_3, x_4, x_5, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_94, x_1, x_99, x_2, x_3, x_4, x_5, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
lean_dec(x_1);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
lean_dec(x_108);
x_1 = x_112;
x_6 = x_111;
goto _start;
}
}
else
{
uint8_t x_114; 
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_99);
x_118 = lean_ctor_get(x_104, 1);
lean_inc(x_118);
lean_dec(x_104);
x_119 = lean_ctor_get(x_105, 0);
lean_inc(x_119);
lean_dec(x_105);
x_120 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_94, x_1, x_119, x_2, x_3, x_4, x_5, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_104);
if (x_121 == 0)
{
return x_104;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_104, 0);
x_123 = lean_ctor_get(x_104, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_104);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_99);
x_125 = lean_ctor_get(x_101, 1);
lean_inc(x_125);
lean_dec(x_101);
x_126 = lean_ctor_get(x_102, 0);
lean_inc(x_126);
lean_dec(x_102);
x_127 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_94, x_1, x_126, x_2, x_3, x_4, x_5, x_125);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_101);
if (x_128 == 0)
{
return x_101;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_101, 0);
x_130 = lean_ctor_get(x_101, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_101);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_98);
if (x_132 == 0)
{
return x_98;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_98, 0);
x_134 = lean_ctor_get(x_98, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_98);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_96, 0);
lean_inc(x_136);
lean_dec(x_96);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_97);
return x_137;
}
}
}
}
case 5:
{
uint8_t x_178; lean_object* x_179; uint8_t x_252; 
x_252 = l_Lean_Expr_hasFVar(x_1);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = l_Lean_Expr_hasExprMVar(x_1);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_2, 0);
lean_inc(x_254);
x_255 = lean_ctor_get_uint8(x_254, 5);
lean_dec(x_254);
x_256 = 2;
x_257 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_255, x_256);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = 1;
x_178 = x_258;
x_179 = x_6;
goto block_251;
}
else
{
uint8_t x_259; 
x_259 = 0;
x_178 = x_259;
x_179 = x_6;
goto block_251;
}
}
else
{
uint8_t x_260; 
x_260 = 0;
x_178 = x_260;
x_179 = x_6;
goto block_251;
}
}
else
{
uint8_t x_261; 
x_261 = 0;
x_178 = x_261;
x_179 = x_6;
goto block_251;
}
block_251:
{
lean_object* x_180; lean_object* x_181; 
if (x_178 == 0)
{
lean_object* x_223; 
x_223 = lean_box(0);
x_180 = x_223;
x_181 = x_179;
goto block_222;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_224 = lean_st_ref_get(x_5, x_179);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_get(x_3, x_225);
x_227 = lean_ctor_get(x_2, 0);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_227, 5);
lean_dec(x_227);
x_229 = lean_box(x_228);
switch (lean_obj_tag(x_229)) {
case 0:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_226, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_dec(x_226);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_232, 4);
lean_inc(x_233);
lean_dec(x_232);
x_234 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_233, x_1);
x_180 = x_234;
x_181 = x_231;
goto block_222;
}
case 1:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
lean_dec(x_226);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_237, 3);
lean_inc(x_238);
lean_dec(x_237);
x_239 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_238, x_1);
x_180 = x_239;
x_181 = x_236;
goto block_222;
}
default: 
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_229);
x_240 = lean_ctor_get(x_226, 1);
lean_inc(x_240);
lean_dec(x_226);
x_241 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_242 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_243 = lean_panic_fn(x_241, x_242);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_244 = lean_apply_5(x_243, x_2, x_3, x_4, x_5, x_240);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_180 = x_245;
x_181 = x_246;
goto block_222;
}
else
{
uint8_t x_247; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_244);
if (x_247 == 0)
{
return x_244;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_244, 0);
x_249 = lean_ctor_get(x_244, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_244);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
}
block_222:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_182; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_182 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_183);
x_185 = l_Lean_Meta_reduceNat_x3f(x_183, x_2, x_3, x_4, x_5, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_183);
x_188 = l_Lean_Meta_reduceNative_x3f(x_183, x_2, x_3, x_4, x_5, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_183);
x_191 = l_Lean_Meta_unfoldDefinition_x3f(x_183, x_2, x_3, x_4, x_5, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_178, x_1, x_183, x_2, x_3, x_4, x_5, x_193);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_183);
lean_dec(x_1);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_1 = x_196;
x_6 = x_195;
goto _start;
}
}
else
{
uint8_t x_198; 
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_191);
if (x_198 == 0)
{
return x_191;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_191, 0);
x_200 = lean_ctor_get(x_191, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_183);
x_202 = lean_ctor_get(x_188, 1);
lean_inc(x_202);
lean_dec(x_188);
x_203 = lean_ctor_get(x_189, 0);
lean_inc(x_203);
lean_dec(x_189);
x_204 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_178, x_1, x_203, x_2, x_3, x_4, x_5, x_202);
return x_204;
}
}
else
{
uint8_t x_205; 
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
return x_188;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_188);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_183);
x_209 = lean_ctor_get(x_185, 1);
lean_inc(x_209);
lean_dec(x_185);
x_210 = lean_ctor_get(x_186, 0);
lean_inc(x_210);
lean_dec(x_186);
x_211 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_178, x_1, x_210, x_2, x_3, x_4, x_5, x_209);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_185);
if (x_212 == 0)
{
return x_185;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_185, 0);
x_214 = lean_ctor_get(x_185, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_185);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_182);
if (x_216 == 0)
{
return x_182;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_182, 0);
x_218 = lean_ctor_get(x_182, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_182);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_180, 0);
lean_inc(x_220);
lean_dec(x_180);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_181);
return x_221;
}
}
}
}
case 8:
{
uint8_t x_262; lean_object* x_263; uint8_t x_336; 
x_336 = l_Lean_Expr_hasFVar(x_1);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = l_Lean_Expr_hasExprMVar(x_1);
if (x_337 == 0)
{
lean_object* x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; 
x_338 = lean_ctor_get(x_2, 0);
lean_inc(x_338);
x_339 = lean_ctor_get_uint8(x_338, 5);
lean_dec(x_338);
x_340 = 2;
x_341 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_339, x_340);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = 1;
x_262 = x_342;
x_263 = x_6;
goto block_335;
}
else
{
uint8_t x_343; 
x_343 = 0;
x_262 = x_343;
x_263 = x_6;
goto block_335;
}
}
else
{
uint8_t x_344; 
x_344 = 0;
x_262 = x_344;
x_263 = x_6;
goto block_335;
}
}
else
{
uint8_t x_345; 
x_345 = 0;
x_262 = x_345;
x_263 = x_6;
goto block_335;
}
block_335:
{
lean_object* x_264; lean_object* x_265; 
if (x_262 == 0)
{
lean_object* x_307; 
x_307 = lean_box(0);
x_264 = x_307;
x_265 = x_263;
goto block_306;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; 
x_308 = lean_st_ref_get(x_5, x_263);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_st_ref_get(x_3, x_309);
x_311 = lean_ctor_get(x_2, 0);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_311, 5);
lean_dec(x_311);
x_313 = lean_box(x_312);
switch (lean_obj_tag(x_313)) {
case 0:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_314 = lean_ctor_get(x_310, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_310, 1);
lean_inc(x_315);
lean_dec(x_310);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_316, 4);
lean_inc(x_317);
lean_dec(x_316);
x_318 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_317, x_1);
x_264 = x_318;
x_265 = x_315;
goto block_306;
}
case 1:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_310, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_310, 1);
lean_inc(x_320);
lean_dec(x_310);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_ctor_get(x_321, 3);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_322, x_1);
x_264 = x_323;
x_265 = x_320;
goto block_306;
}
default: 
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_313);
x_324 = lean_ctor_get(x_310, 1);
lean_inc(x_324);
lean_dec(x_310);
x_325 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_326 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_327 = lean_panic_fn(x_325, x_326);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_328 = lean_apply_5(x_327, x_2, x_3, x_4, x_5, x_324);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_264 = x_329;
x_265 = x_330;
goto block_306;
}
else
{
uint8_t x_331; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_328);
if (x_331 == 0)
{
return x_328;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_328, 0);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_328);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
}
block_306:
{
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_266; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_266 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_267);
x_269 = l_Lean_Meta_reduceNat_x3f(x_267, x_2, x_3, x_4, x_5, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_267);
x_272 = l_Lean_Meta_reduceNative_x3f(x_267, x_2, x_3, x_4, x_5, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_267);
x_275 = l_Lean_Meta_unfoldDefinition_x3f(x_267, x_2, x_3, x_4, x_5, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_262, x_1, x_267, x_2, x_3, x_4, x_5, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_267);
lean_dec(x_1);
x_279 = lean_ctor_get(x_275, 1);
lean_inc(x_279);
lean_dec(x_275);
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
lean_dec(x_276);
x_1 = x_280;
x_6 = x_279;
goto _start;
}
}
else
{
uint8_t x_282; 
lean_dec(x_267);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_282 = !lean_is_exclusive(x_275);
if (x_282 == 0)
{
return x_275;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_275, 0);
x_284 = lean_ctor_get(x_275, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_275);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_267);
x_286 = lean_ctor_get(x_272, 1);
lean_inc(x_286);
lean_dec(x_272);
x_287 = lean_ctor_get(x_273, 0);
lean_inc(x_287);
lean_dec(x_273);
x_288 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_262, x_1, x_287, x_2, x_3, x_4, x_5, x_286);
return x_288;
}
}
else
{
uint8_t x_289; 
lean_dec(x_267);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_272);
if (x_289 == 0)
{
return x_272;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_272, 0);
x_291 = lean_ctor_get(x_272, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_272);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_267);
x_293 = lean_ctor_get(x_269, 1);
lean_inc(x_293);
lean_dec(x_269);
x_294 = lean_ctor_get(x_270, 0);
lean_inc(x_294);
lean_dec(x_270);
x_295 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_262, x_1, x_294, x_2, x_3, x_4, x_5, x_293);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_267);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_269);
if (x_296 == 0)
{
return x_269;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_269, 0);
x_298 = lean_ctor_get(x_269, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_269);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_266);
if (x_300 == 0)
{
return x_266;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_266, 0);
x_302 = lean_ctor_get(x_266, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_266);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_264, 0);
lean_inc(x_304);
lean_dec(x_264);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_265);
return x_305;
}
}
}
}
case 10:
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_1, 1);
lean_inc(x_346);
lean_dec(x_1);
x_1 = x_346;
goto _start;
}
case 11:
{
uint8_t x_348; lean_object* x_349; uint8_t x_422; 
x_422 = l_Lean_Expr_hasFVar(x_1);
if (x_422 == 0)
{
uint8_t x_423; 
x_423 = l_Lean_Expr_hasExprMVar(x_1);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; uint8_t x_426; uint8_t x_427; 
x_424 = lean_ctor_get(x_2, 0);
lean_inc(x_424);
x_425 = lean_ctor_get_uint8(x_424, 5);
lean_dec(x_424);
x_426 = 2;
x_427 = l___private_Lean_Meta_TransparencyMode_0__Lean_Meta_beqTransparencyMode____x40_Lean_Meta_TransparencyMode___hyg_11_(x_425, x_426);
if (x_427 == 0)
{
uint8_t x_428; 
x_428 = 1;
x_348 = x_428;
x_349 = x_6;
goto block_421;
}
else
{
uint8_t x_429; 
x_429 = 0;
x_348 = x_429;
x_349 = x_6;
goto block_421;
}
}
else
{
uint8_t x_430; 
x_430 = 0;
x_348 = x_430;
x_349 = x_6;
goto block_421;
}
}
else
{
uint8_t x_431; 
x_431 = 0;
x_348 = x_431;
x_349 = x_6;
goto block_421;
}
block_421:
{
lean_object* x_350; lean_object* x_351; 
if (x_348 == 0)
{
lean_object* x_393; 
x_393 = lean_box(0);
x_350 = x_393;
x_351 = x_349;
goto block_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_394 = lean_st_ref_get(x_5, x_349);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_st_ref_get(x_3, x_395);
x_397 = lean_ctor_get(x_2, 0);
lean_inc(x_397);
x_398 = lean_ctor_get_uint8(x_397, 5);
lean_dec(x_397);
x_399 = lean_box(x_398);
switch (lean_obj_tag(x_399)) {
case 0:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_396, 1);
lean_inc(x_401);
lean_dec(x_396);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_ctor_get(x_402, 4);
lean_inc(x_403);
lean_dec(x_402);
x_404 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_403, x_1);
x_350 = x_404;
x_351 = x_401;
goto block_392;
}
case 1:
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = lean_ctor_get(x_396, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_396, 1);
lean_inc(x_406);
lean_dec(x_396);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_407, 3);
lean_inc(x_408);
lean_dec(x_407);
x_409 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_408, x_1);
x_350 = x_409;
x_351 = x_406;
goto block_392;
}
default: 
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_399);
x_410 = lean_ctor_get(x_396, 1);
lean_inc(x_410);
lean_dec(x_396);
x_411 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_412 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_413 = lean_panic_fn(x_411, x_412);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_414 = lean_apply_5(x_413, x_2, x_3, x_4, x_5, x_410);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_350 = x_415;
x_351 = x_416;
goto block_392;
}
else
{
uint8_t x_417; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_414);
if (x_417 == 0)
{
return x_414;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_414, 0);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_414);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
}
block_392:
{
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_352; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_352 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_353);
x_355 = l_Lean_Meta_reduceNat_x3f(x_353, x_2, x_3, x_4, x_5, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_353);
x_358 = l_Lean_Meta_reduceNative_x3f(x_353, x_2, x_3, x_4, x_5, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_353);
x_361 = l_Lean_Meta_unfoldDefinition_x3f(x_353, x_2, x_3, x_4, x_5, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_348, x_1, x_353, x_2, x_3, x_4, x_5, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_353);
lean_dec(x_1);
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
lean_dec(x_361);
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
lean_dec(x_362);
x_1 = x_366;
x_6 = x_365;
goto _start;
}
}
else
{
uint8_t x_368; 
lean_dec(x_353);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_361);
if (x_368 == 0)
{
return x_361;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_361, 0);
x_370 = lean_ctor_get(x_361, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_361);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_353);
x_372 = lean_ctor_get(x_358, 1);
lean_inc(x_372);
lean_dec(x_358);
x_373 = lean_ctor_get(x_359, 0);
lean_inc(x_373);
lean_dec(x_359);
x_374 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_348, x_1, x_373, x_2, x_3, x_4, x_5, x_372);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_353);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_375 = !lean_is_exclusive(x_358);
if (x_375 == 0)
{
return x_358;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_358, 0);
x_377 = lean_ctor_get(x_358, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_358);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_353);
x_379 = lean_ctor_get(x_355, 1);
lean_inc(x_379);
lean_dec(x_355);
x_380 = lean_ctor_get(x_356, 0);
lean_inc(x_380);
lean_dec(x_356);
x_381 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_348, x_1, x_380, x_2, x_3, x_4, x_5, x_379);
return x_381;
}
}
else
{
uint8_t x_382; 
lean_dec(x_353);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_355);
if (x_382 == 0)
{
return x_355;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_355, 0);
x_384 = lean_ctor_get(x_355, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_355);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = !lean_is_exclusive(x_352);
if (x_386 == 0)
{
return x_352;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_352, 0);
x_388 = lean_ctor_get(x_352, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_352);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = lean_ctor_get(x_350, 0);
lean_inc(x_390);
lean_dec(x_350);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_351);
return x_391;
}
}
}
}
default: 
{
lean_object* x_432; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_1);
lean_ctor_set(x_432, 1, x_6);
return x_432;
}
}
}
}
lean_object* l_Lean_Meta_whnfImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_setWHNFRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setWHNFRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Meta_whnfRef;
x_3 = l_Lean_Meta_setWHNFRef___closed__1;
x_4 = lean_st_ref_set(x_2, x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4937_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_ToExpr(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Meta_GetConst(lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_WHNF(lean_object* w) {
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
l_Lean_Meta_smartUnfoldingDefault = _init_l_Lean_Meta_smartUnfoldingDefault();
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__5);
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__3);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__4);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2___closed__5);
l_Lean_Meta_reduceRecMatcher_x3f___closed__1 = _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_reduceRecMatcher_x3f___closed__1);
l_Lean_Meta_reduceRecMatcher_x3f___closed__2 = _init_l_Lean_Meta_reduceRecMatcher_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_reduceRecMatcher_x3f___closed__2);
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
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2);
l_Lean_Meta_setWHNFRef___closed__1 = _init_l_Lean_Meta_setWHNFRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setWHNFRef___closed__1);
res = l_Lean_Meta_setWHNFRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4937_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
