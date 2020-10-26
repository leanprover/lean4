// Lean compiler output
// Module: Lean.Meta.WHNF
// Imports: Init Lean.ToExpr Lean.AuxRecursor Lean.Meta.Basic Lean.Meta.LevelDefEq
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___boxed(lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l_Lean_Meta_whnfImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__2(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__3;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__16;
extern lean_object* l_Lean_Lean_ToExpr___instance__9___rarg___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
lean_object* l_Lean_Meta_withNatValue(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Meta_unfoldDefinition_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__5;
extern lean_object* l_Lean_Lean_ToExpr___instance__9___rarg___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__7;
extern lean_object* l_Nat_Init_Data_Nat_Div___instance__1___closed__1;
lean_object* l_Lean_Meta_whnfImp_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__10;
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3(lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__3;
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object*);
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__3(lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_995____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__6;
extern lean_object* l_Lean_auxRecExt;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__4(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_smartUnfoldingSuffix;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__5(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
lean_object* l_Lean_Meta_reduceNat_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3(lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_withNatValue_match__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_Exception___instance__1___closed__1;
lean_object* l_Lean_Meta_whnfImp_match__2(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__10;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2(lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_516____closed__2;
lean_object* l_Lean_Meta_reduceNative_x3f___closed__3;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__7;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
lean_object* l_Lean_Meta_toCtorIfLit___closed__9;
lean_object* l_Lean_Meta_smartUnfoldingSuffix___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3(lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Init_Data_Nat_Div___instance__2___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
lean_object* l_Lean_Meta_reduceNative_x3f_match__1(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
extern lean_object* l_Init_Core___instance__2___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__17;
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4523_(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__11;
lean_object* l_Lean_Meta_whnfHeadPred(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1(lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1(lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__2;
lean_object* l_Lean_Meta_toCtorIfLit___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
lean_object* l_Lean_Meta_toCtorIfLit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__13;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp(lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__4;
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
lean_object* l_Lean_Meta_whnfHeadPredImp_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__11;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Init_Data_Nat_Basic___instance__5___closed__1;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__8;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1(lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
lean_object* l_Lean_Meta_whnfCore(lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__2;
lean_object* l_Lean_Meta_toCtorIfLit___closed__6;
lean_object* l_Lean_Meta_withNatValue_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__15;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2(lean_object*);
extern lean_object* l_Lean_Expr_isCharLit___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1(lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__1;
lean_object* l_Lean_Meta_mkSmartUnfoldingNameFor(lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__5;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__4___lambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1(lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__4;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__9;
extern lean_object* l_Nat_Init_Data_Nat_Basic___instance__4___closed__1;
lean_object* l_Lean_Meta_whnfUntil(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
lean_object* l_Lean_Meta_getConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPred___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__17___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_isAuxDef_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isAuxDef_x3f___rarg), 2, 0);
return x_2;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
lean_dec(x_6);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_box(x_13);
x_22 = lean_box(x_14);
x_23 = lean_box(x_15);
x_24 = lean_apply_11(x_2, x_19, x_20, x_16, x_17, x_18, x_10, x_11, x_12, x_21, x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_2);
x_25 = lean_apply_1(x_3, x_1);
return x_25;
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
x_32 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_31, x_31, x_24, x_23);
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
x_43 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_42, x_42, x_35, x_34);
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
x_57 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_56, x_56, x_49, x_48);
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
x_9 = l_Lean_Lean_ToExpr___instance__4___lambda__1___closed__1;
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
x_1 = lean_mk_string("succ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_toCtorIfLit___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__17___closed__2;
x_2 = l_Lean_Init_LeanInit___instance__19___rarg___closed__3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isCharLit___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lean_ToExpr___instance__9___rarg___closed__1;
x_2 = l_Lean_Meta_toCtorIfLit___closed__9;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lean_ToExpr___instance__9___rarg___closed__2;
x_2 = l_Lean_Meta_toCtorIfLit___closed__9;
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
x_9 = l_Lean_Meta_toCtorIfLit___closed__3;
x_10 = l_Lean_mkApp(x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_Meta_toCtorIfLit___closed__6;
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
x_14 = l_Lean_Meta_toCtorIfLit___closed__10;
x_15 = l_Lean_Meta_toCtorIfLit___closed__11;
x_16 = l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(x_14, x_15, x_13);
x_17 = l_Lean_Meta_toCtorIfLit___closed__8;
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
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_hasExprMVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_Expr_hasExprMVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
x_13 = 1;
return x_13;
}
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
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = l_Lean_Expr_getAppFn(x_12);
x_16 = l_Lean_RecursorVal_getInduct(x_1);
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_91; uint8_t x_92; 
x_20 = l_Lean_Expr_hasExprMVar(x_12);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Expr_getAppNumArgsAux(x_12, x_21);
x_23 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
lean_inc(x_12);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_24, x_26);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_91 = lean_array_get_size(x_27);
x_92 = lean_nat_dec_le(x_91, x_91);
if (x_92 == 0)
{
if (x_20 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_27);
lean_dec(x_14);
lean_inc(x_12);
x_93 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_12, x_28, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_28);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
lean_dec(x_93);
x_102 = !lean_is_exclusive(x_94);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_94, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_103);
x_104 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_103, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_105, x_3, x_4, x_5, x_6, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
lean_free_object(x_94);
lean_dec(x_103);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_107, 0);
lean_dec(x_111);
x_112 = lean_box(0);
lean_ctor_set(x_107, 0, x_112);
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_107);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_107, 0);
lean_dec(x_117);
lean_ctor_set(x_107, 0, x_94);
return x_107;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
lean_dec(x_107);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_94);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_free_object(x_94);
lean_dec(x_103);
x_120 = !lean_is_exclusive(x_107);
if (x_120 == 0)
{
return x_107;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_107, 0);
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_107);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_94);
lean_dec(x_103);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_104);
if (x_124 == 0)
{
return x_104;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_104, 0);
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_104);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_94, 0);
lean_inc(x_128);
lean_dec(x_94);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_128);
x_129 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_128, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_130, x_3, x_4, x_5, x_6, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_128);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_128);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_128);
x_143 = lean_ctor_get(x_132, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_132, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_145 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_128);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = lean_ctor_get(x_129, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_129, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_149 = x_129;
} else {
 lean_dec_ref(x_129);
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
}
else
{
uint8_t x_151; 
lean_inc(x_28);
x_151 = l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_12, x_27, x_91, x_28);
lean_dec(x_91);
lean_dec(x_27);
x_29 = x_151;
goto block_90;
}
}
else
{
if (x_20 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_91);
lean_dec(x_27);
lean_dec(x_14);
lean_inc(x_12);
x_152 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_12, x_28, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_28);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 0);
lean_dec(x_155);
x_156 = lean_box(0);
lean_ctor_set(x_152, 0, x_156);
return x_152;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_dec(x_152);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
lean_dec(x_152);
x_161 = !lean_is_exclusive(x_153);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_153, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_162);
x_163 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_162, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_164, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_free_object(x_153);
lean_dec(x_162);
x_169 = !lean_is_exclusive(x_166);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_166, 0);
lean_dec(x_170);
x_171 = lean_box(0);
lean_ctor_set(x_166, 0, x_171);
return x_166;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_dec(x_166);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_166);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_166, 0);
lean_dec(x_176);
lean_ctor_set(x_166, 0, x_153);
return x_166;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_166, 1);
lean_inc(x_177);
lean_dec(x_166);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_153);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_free_object(x_153);
lean_dec(x_162);
x_179 = !lean_is_exclusive(x_166);
if (x_179 == 0)
{
return x_166;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_166, 0);
x_181 = lean_ctor_get(x_166, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_166);
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
lean_free_object(x_153);
lean_dec(x_162);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_163);
if (x_183 == 0)
{
return x_163;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_163, 0);
x_185 = lean_ctor_get(x_163, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_163);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_153, 0);
lean_inc(x_187);
lean_dec(x_153);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_187);
x_188 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_187, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_189, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_187);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_195 = x_191;
} else {
 lean_dec_ref(x_191);
 x_195 = lean_box(0);
}
x_196 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_191, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_187);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_187);
x_202 = lean_ctor_get(x_191, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_191, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_204 = x_191;
} else {
 lean_dec_ref(x_191);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_187);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = lean_ctor_get(x_188, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_208 = x_188;
} else {
 lean_dec_ref(x_188);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_inc(x_28);
x_210 = l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(x_12, lean_box(0), x_27, x_91, x_28);
lean_dec(x_91);
lean_dec(x_27);
x_29 = x_210;
goto block_90;
}
}
block_90:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
lean_inc(x_12);
x_30 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_12, x_28, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_41 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_40, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_42, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
lean_free_object(x_31);
lean_dec(x_40);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_44, 0);
lean_dec(x_54);
lean_ctor_set(x_44, 0, x_31);
return x_44;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_31);
lean_dec(x_40);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_31);
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_65);
x_66 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_65, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_12, x_67, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_65);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
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
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_65);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_65);
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_82 = x_69;
} else {
 lean_dec_ref(x_69);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_65);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_86 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_14;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_13);
return x_89;
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_11);
if (x_211 == 0)
{
return x_11;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_11, 0);
x_213 = lean_ctor_get(x_11, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_11);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_8);
if (x_215 == 0)
{
return x_8;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_8, 0);
x_217 = lean_ctor_get(x_8, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_8);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_17 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_16, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_RecursorVal_getMajorIdx(x_2);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_4, x_11);
lean_dec(x_11);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_18 = l_Lean_Meta_whnf___rarg(x_17, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_apply_5(x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_1, x_20, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
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
x_19 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_18, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Expr_Lean_Expr___instance__11;
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
x_72 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_71, x_6, x_7, x_8, x_9, x_10);
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
x_90 = l_Lean_Expr_Lean_Expr___instance__11;
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_11 = lean_box(x_10);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fget(x_4, x_13);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_19 = l_Lean_Meta_whnf___rarg(x_18, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_apply_5(x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_1, x_21, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_4);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_dec_lt(x_29, x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_array_fget(x_4, x_29);
x_34 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_35 = l_Lean_Meta_whnf___rarg(x_34, x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = lean_apply_5(x_35, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_6(x_1, x_37, x_5, x_6, x_7, x_8, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
default: 
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(x_18, x_4, x_5, x_6, x_7, x_19);
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
x_31 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_30, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(x_32, x_4, x_5, x_6, x_7, x_33);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(x_17, x_4, x_5, x_6, x_7, x_18);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Meta_getConstNoEx_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
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
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
switch (lean_obj_tag(x_25)) {
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux(x_1, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_31, x_33);
x_35 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1(x_27, x_16, x_34, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_34);
lean_dec(x_16);
lean_dec(x_27);
return x_35;
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Expr_getAppNumArgsAux(x_1, x_38);
x_40 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_41, x_43);
x_45 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2(x_37, x_16, x_44, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_37);
return x_45;
}
default: 
{
uint8_t x_46; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_17, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_17, 0, x_48);
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
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
}
case 10:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_1 = x_54;
goto _start;
}
case 11:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_56, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_1 = x_58;
x_6 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
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
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getStuckMVar_x3f___rarg), 2, 0);
return x_2;
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
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
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_7, x_1, x_16, x_18, x_2);
return x_19;
}
case 1:
{
lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
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
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_4(x_10, x_1, x_20, x_22, x_2);
return x_23;
}
case 2:
{
lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
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
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_26 = lean_box_uint64(x_25);
x_27 = lean_apply_4(x_11, x_1, x_24, x_26, x_2);
return x_27;
}
case 3:
{
lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
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
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_4(x_5, x_1, x_28, x_30, x_2);
return x_31;
}
case 4:
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
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
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_35 = lean_box_uint64(x_34);
x_36 = lean_apply_5(x_12, x_1, x_32, x_33, x_35, x_2);
return x_36;
}
case 5:
{
lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
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
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_40 = lean_box_uint64(x_39);
x_41 = lean_apply_5(x_13, x_1, x_37, x_38, x_40, x_2);
return x_41;
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
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
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_46 = lean_box_uint64(x_45);
x_47 = lean_apply_6(x_4, x_1, x_42, x_43, x_44, x_46, x_2);
return x_47;
}
case 7:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_15);
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
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_52 = lean_box_uint64(x_51);
x_53 = lean_apply_6(x_3, x_1, x_48, x_49, x_50, x_52, x_2);
return x_53;
}
case 8:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_15);
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
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 3);
lean_inc(x_57);
x_58 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_59 = lean_box_uint64(x_58);
x_60 = lean_apply_7(x_9, x_1, x_54, x_55, x_56, x_57, x_59, x_2);
return x_60;
}
case 9:
{
lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_15);
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
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_63 = lean_box_uint64(x_62);
x_64 = lean_apply_4(x_6, x_1, x_61, x_63, x_2);
return x_64;
}
case 10:
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_15);
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
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_68 = lean_box_uint64(x_67);
x_69 = lean_apply_4(x_8, x_65, x_66, x_68, x_2);
return x_69;
}
case 11:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
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
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_74 = lean_box_uint64(x_73);
x_75 = lean_apply_6(x_14, x_1, x_70, x_71, x_72, x_74, x_2);
return x_75;
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
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
lean_dec(x_3);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_80 = lean_box_uint64(x_79);
x_81 = lean_apply_5(x_15, x_76, x_77, x_78, x_80, x_2);
return x_81;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg), 15, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.WHNF");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.whnfEasyCases");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_3 = lean_unsigned_to_nat(204u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_3 = lean_unsigned_to_nat(226u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
lean_inc(x_12);
x_14 = l_Lean_Meta_getLocalDecl___rarg(x_13, x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_5(x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 4);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
lean_dec(x_16);
x_24 = l_Lean_Meta_getConfig___rarg___lambda__1(x_3, x_4, x_5, x_6, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, 6);
if (x_26 == 0)
{
if (x_23 == 0)
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get_uint8(x_25, 7);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_12);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_1 = x_22;
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
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
x_1 = x_22;
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
x_1 = x_22;
x_7 = x_49;
goto _start;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_24, 0);
lean_dec(x_52);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_dec(x_24);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_1);
x_55 = lean_ctor_get_uint8(x_25, 7);
lean_dec(x_25);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_12);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_1 = x_22;
x_7 = x_56;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_st_ref_take(x_4, x_58);
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
x_64 = lean_box(0);
x_65 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_63, x_12, x_64);
lean_ctor_set(x_60, 2, x_65);
x_66 = lean_st_ref_set(x_4, x_60, x_61);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_1 = x_22;
x_7 = x_67;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
x_71 = lean_ctor_get(x_60, 2);
x_72 = lean_ctor_get(x_60, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
x_73 = lean_box(0);
x_74 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_71, x_12, x_73);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_72);
x_76 = lean_st_ref_set(x_4, x_75, x_61);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_1 = x_22;
x_7 = x_77;
goto _start;
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 2:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
x_84 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_85 = l_Lean_Meta_getExprMVarAssignment_x3f___rarg(x_84, x_83);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_86 = lean_apply_5(x_85, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
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
else
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_86);
if (x_95 == 0)
{
return x_86;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_86, 0);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_86);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 4:
{
lean_object* x_99; 
x_99 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_99;
}
case 5:
{
lean_object* x_100; 
x_100 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_100;
}
case 8:
{
lean_object* x_101; 
x_101 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_101;
}
case 10:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
lean_dec(x_1);
x_1 = x_102;
goto _start;
}
case 11:
{
lean_object* x_104; 
x_104 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_104;
}
case 12:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_2);
lean_dec(x_1);
x_105 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_106 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_107 = lean_panic_fn(x_105, x_106);
x_108 = lean_apply_5(x_107, x_3, x_4, x_5, x_6, x_7);
return x_108;
}
default: 
{
lean_object* x_109; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_7);
return x_109;
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
x_13 = l_Lean_Expr_Lean_Expr___instance__11;
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_4(x_2, x_1, x_7, x_8, x_10);
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
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_4, x_1, x_12, x_13, x_15);
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
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_6(x_3, x_1, x_17, x_18, x_19, x_20, x_22);
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
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_5(x_5, x_1, x_24, x_25, x_26, x_28);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_23, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_516____closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.whnfCoreImp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_3 = lean_unsigned_to_nat(295u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
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
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(x_2, x_3, x_4, x_5, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, 6);
if (x_23 == 0)
{
if (x_20 == 0)
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_1 = x_19;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_st_ref_take(x_3, x_27);
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
x_33 = lean_box(0);
x_34 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_32, x_11, x_33);
lean_ctor_set(x_29, 2, x_34);
x_35 = lean_st_ref_set(x_3, x_29, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_1 = x_19;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
x_41 = lean_ctor_get(x_29, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_42 = lean_box(0);
x_43 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_11, x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_41);
x_45 = lean_st_ref_set(x_3, x_44, x_30);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_1 = x_19;
x_6 = x_46;
goto _start;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_21, 0);
lean_dec(x_49);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_1);
x_52 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_11);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_dec(x_21);
x_1 = x_19;
x_6 = x_53;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_st_ref_take(x_3, x_55);
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
x_61 = lean_box(0);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_60, x_11, x_61);
lean_ctor_set(x_57, 2, x_62);
x_63 = lean_st_ref_set(x_3, x_57, x_58);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_1 = x_19;
x_6 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
x_68 = lean_ctor_get(x_57, 2);
x_69 = lean_ctor_get(x_57, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_70 = lean_box(0);
x_71 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_68, x_11, x_70);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_69);
x_73 = lean_st_ref_set(x_3, x_72, x_58);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_1 = x_19;
x_6 = x_74;
goto _start;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_12);
if (x_76 == 0)
{
return x_12;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_80, x_2, x_3, x_4, x_5, x_6);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_1 = x_88;
x_6 = x_87;
goto _start;
}
}
case 4:
{
lean_object* x_90; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_350 = lean_st_ref_get(x_5, x_6);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_351, 3);
lean_inc(x_352);
lean_dec(x_351);
x_353 = lean_ctor_get_uint8(x_352, sizeof(void*)*1);
lean_dec(x_352);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
lean_dec(x_350);
x_90 = x_354;
goto block_349;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_355 = lean_ctor_get(x_350, 1);
lean_inc(x_355);
lean_dec(x_350);
x_356 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_357 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_356, x_2, x_3, x_4, x_5, x_355);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_unbox(x_358);
lean_dec(x_358);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_90 = x_360;
goto block_349;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
lean_dec(x_357);
lean_inc(x_1);
x_362 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_362, 0, x_1);
x_363 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_356, x_362, x_2, x_3, x_4, x_5, x_361);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_90 = x_364;
goto block_349;
}
}
block_349:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_91; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
case 5:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = l_Lean_Expr_getAppFn(x_92);
lean_dec(x_92);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_93);
x_94 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_93, x_2, x_3, x_4, x_5, x_90);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = l_Lean_Expr_isLambda(x_96);
if (x_98 == 0)
{
if (lean_obj_tag(x_96) == 4)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_free_object(x_94);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_1);
lean_inc(x_96);
lean_inc(x_93);
x_101 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_101, 0, x_93);
lean_closure_set(x_101, 1, x_96);
lean_closure_set(x_101, 2, x_1);
x_102 = l_Lean_Meta_getConst_x3f(x_99, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
lean_ctor_set(x_102, 0, x_107);
return x_102;
}
else
{
lean_dec(x_96);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_dec(x_102);
x_109 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_96);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
}
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
lean_dec(x_103);
switch (lean_obj_tag(x_113)) {
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_101);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_dec(x_102);
x_115 = l_Lean_ConstantInfo_name(x_113);
x_116 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_115, x_2, x_3, x_4, x_5, x_114);
lean_dec(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_113);
lean_dec(x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_116, 0);
lean_dec(x_120);
x_121 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
lean_ctor_set(x_116, 0, x_122);
return x_116;
}
else
{
lean_dec(x_96);
lean_ctor_set(x_116, 0, x_1);
return x_116;
}
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; 
lean_dec(x_96);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_123);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
lean_dec(x_116);
x_129 = lean_unsigned_to_nat(0u);
x_130 = l_Lean_Expr_getAppNumArgsAux(x_1, x_129);
x_131 = lean_mk_empty_array_with_capacity(x_130);
lean_dec(x_130);
lean_inc(x_1);
x_132 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_131);
x_133 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_93, x_96, x_113, x_100, x_132, x_2, x_3, x_4, x_5, x_128);
lean_dec(x_132);
lean_dec(x_100);
lean_dec(x_113);
lean_dec(x_96);
lean_dec(x_93);
return x_133;
}
}
case 4:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_96);
lean_dec(x_93);
x_134 = lean_ctor_get(x_102, 1);
lean_inc(x_134);
lean_dec(x_102);
x_135 = lean_ctor_get(x_113, 0);
lean_inc(x_135);
lean_dec(x_113);
x_136 = lean_unsigned_to_nat(0u);
x_137 = l_Lean_Expr_getAppNumArgsAux(x_1, x_136);
x_138 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_137);
x_139 = lean_mk_array(x_137, x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_137, x_140);
lean_dec(x_137);
x_142 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_139, x_141);
x_143 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_144 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_135, x_100, x_142, x_101, x_143, x_2, x_3, x_4, x_5, x_134);
lean_dec(x_142);
lean_dec(x_100);
lean_dec(x_135);
return x_144;
}
case 7:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_96);
lean_dec(x_93);
x_145 = lean_ctor_get(x_102, 1);
lean_inc(x_145);
lean_dec(x_102);
x_146 = lean_ctor_get(x_113, 0);
lean_inc(x_146);
lean_dec(x_113);
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Lean_Expr_getAppNumArgsAux(x_1, x_147);
x_149 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_148);
x_150 = lean_mk_array(x_148, x_149);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_sub(x_148, x_151);
lean_dec(x_148);
x_153 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_150, x_152);
x_154 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_155 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_146, x_100, x_153, x_101, x_154, x_2, x_3, x_4, x_5, x_145);
lean_dec(x_153);
lean_dec(x_100);
return x_155;
}
default: 
{
uint8_t x_156; 
lean_dec(x_113);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_102);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_102, 0);
lean_dec(x_157);
x_158 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
lean_ctor_set(x_102, 0, x_159);
return x_102;
}
else
{
lean_dec(x_96);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_102, 1);
lean_inc(x_160);
lean_dec(x_102);
x_161 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_96);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
}
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_102);
if (x_165 == 0)
{
return x_102;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_102, 0);
x_167 = lean_ctor_get(x_102, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_102);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_expr_eqv(x_93, x_96);
lean_dec(x_93);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = l_Lean_Expr_updateFn(x_1, x_96);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_170);
return x_94;
}
else
{
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_1);
return x_94;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_free_object(x_94);
lean_dec(x_93);
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Lean_Expr_getAppNumArgsAux(x_1, x_171);
x_173 = lean_mk_empty_array_with_capacity(x_172);
lean_dec(x_172);
x_174 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_173);
x_175 = l_Lean_Expr_betaRev(x_96, x_174);
lean_dec(x_174);
lean_dec(x_96);
x_1 = x_175;
x_6 = x_97;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_94, 0);
x_178 = lean_ctor_get(x_94, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_94);
x_179 = l_Lean_Expr_isLambda(x_177);
if (x_179 == 0)
{
if (lean_obj_tag(x_177) == 4)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_inc(x_1);
lean_inc(x_177);
lean_inc(x_93);
x_182 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_182, 0, x_93);
lean_closure_set(x_182, 1, x_177);
lean_closure_set(x_182, 2, x_1);
x_183 = l_Lean_Meta_getConst_x3f(x_180, x_2, x_3, x_4, x_5, x_178);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_expr_eqv(x_93, x_177);
lean_dec(x_93);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Lean_Expr_updateFn(x_1, x_177);
lean_dec(x_177);
if (lean_is_scalar(x_186)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_186;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_185);
return x_189;
}
else
{
lean_object* x_190; 
lean_dec(x_177);
if (lean_is_scalar(x_186)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_186;
}
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_185);
return x_190;
}
}
else
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_184, 0);
lean_inc(x_191);
lean_dec(x_184);
switch (lean_obj_tag(x_191)) {
case 1:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_182);
x_192 = lean_ctor_get(x_183, 1);
lean_inc(x_192);
lean_dec(x_183);
x_193 = l_Lean_ConstantInfo_name(x_191);
x_194 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_193, x_2, x_3, x_4, x_5, x_192);
lean_dec(x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_191);
lean_dec(x_181);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_198 = x_194;
} else {
 lean_dec_ref(x_194);
 x_198 = lean_box(0);
}
x_199 = lean_expr_eqv(x_93, x_177);
lean_dec(x_93);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Lean_Expr_updateFn(x_1, x_177);
lean_dec(x_177);
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
else
{
lean_object* x_202; 
lean_dec(x_177);
if (lean_is_scalar(x_198)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_198;
}
lean_ctor_set(x_202, 0, x_1);
lean_ctor_set(x_202, 1, x_197);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
lean_dec(x_194);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Lean_Expr_getAppNumArgsAux(x_1, x_204);
x_206 = lean_mk_empty_array_with_capacity(x_205);
lean_dec(x_205);
lean_inc(x_1);
x_207 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_206);
x_208 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_93, x_177, x_191, x_181, x_207, x_2, x_3, x_4, x_5, x_203);
lean_dec(x_207);
lean_dec(x_181);
lean_dec(x_191);
lean_dec(x_177);
lean_dec(x_93);
return x_208;
}
}
case 4:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_177);
lean_dec(x_93);
x_209 = lean_ctor_get(x_183, 1);
lean_inc(x_209);
lean_dec(x_183);
x_210 = lean_ctor_get(x_191, 0);
lean_inc(x_210);
lean_dec(x_191);
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Lean_Expr_getAppNumArgsAux(x_1, x_211);
x_213 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_212);
x_214 = lean_mk_array(x_212, x_213);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_nat_sub(x_212, x_215);
lean_dec(x_212);
x_217 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_214, x_216);
x_218 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_219 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_210, x_181, x_217, x_182, x_218, x_2, x_3, x_4, x_5, x_209);
lean_dec(x_217);
lean_dec(x_181);
lean_dec(x_210);
return x_219;
}
case 7:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_177);
lean_dec(x_93);
x_220 = lean_ctor_get(x_183, 1);
lean_inc(x_220);
lean_dec(x_183);
x_221 = lean_ctor_get(x_191, 0);
lean_inc(x_221);
lean_dec(x_191);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l_Lean_Expr_getAppNumArgsAux(x_1, x_222);
x_224 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_223);
x_225 = lean_mk_array(x_223, x_224);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_nat_sub(x_223, x_226);
lean_dec(x_223);
x_228 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_225, x_227);
x_229 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_230 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_221, x_181, x_228, x_182, x_229, x_2, x_3, x_4, x_5, x_220);
lean_dec(x_228);
lean_dec(x_181);
return x_230;
}
default: 
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec(x_191);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_183, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_232 = x_183;
} else {
 lean_dec_ref(x_183);
 x_232 = lean_box(0);
}
x_233 = lean_expr_eqv(x_93, x_177);
lean_dec(x_93);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Lean_Expr_updateFn(x_1, x_177);
lean_dec(x_177);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_232;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_231);
return x_235;
}
else
{
lean_object* x_236; 
lean_dec(x_177);
if (lean_is_scalar(x_232)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_232;
}
lean_ctor_set(x_236, 0, x_1);
lean_ctor_set(x_236, 1, x_231);
return x_236;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_183, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_183, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_239 = x_183;
} else {
 lean_dec_ref(x_183);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
uint8_t x_241; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_241 = lean_expr_eqv(x_93, x_177);
lean_dec(x_93);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = l_Lean_Expr_updateFn(x_1, x_177);
lean_dec(x_177);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_178);
return x_243;
}
else
{
lean_object* x_244; 
lean_dec(x_177);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_1);
lean_ctor_set(x_244, 1, x_178);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_93);
x_245 = lean_unsigned_to_nat(0u);
x_246 = l_Lean_Expr_getAppNumArgsAux(x_1, x_245);
x_247 = lean_mk_empty_array_with_capacity(x_246);
lean_dec(x_246);
x_248 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_247);
x_249 = l_Lean_Expr_betaRev(x_177, x_248);
lean_dec(x_248);
lean_dec(x_177);
x_1 = x_249;
x_6 = x_178;
goto _start;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_94);
if (x_251 == 0)
{
return x_94;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_94, 0);
x_253 = lean_ctor_get(x_94, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_94);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
case 8:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_1, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_1, 3);
lean_inc(x_256);
lean_dec(x_1);
x_257 = lean_expr_instantiate1(x_256, x_255);
lean_dec(x_255);
lean_dec(x_256);
x_1 = x_257;
x_6 = x_90;
goto _start;
}
case 11:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_1, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 2);
lean_inc(x_260);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_261 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_260, x_2, x_3, x_4, x_5, x_90);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_ctor_get(x_261, 1);
x_265 = l_Lean_Expr_getAppFn(x_263);
if (lean_obj_tag(x_265) == 4)
{
lean_object* x_266; lean_object* x_267; 
lean_free_object(x_261);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec(x_265);
x_267 = l_Lean_Meta_getConst_x3f(x_266, x_2, x_3, x_4, x_5, x_264);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
lean_dec(x_263);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_267, 0);
lean_dec(x_270);
lean_ctor_set(x_267, 0, x_1);
return x_267;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
lean_dec(x_268);
if (lean_obj_tag(x_273) == 6)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_267);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_275 = lean_ctor_get(x_267, 1);
x_276 = lean_ctor_get(x_267, 0);
lean_dec(x_276);
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
lean_dec(x_273);
x_278 = lean_ctor_get(x_277, 3);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_nat_add(x_278, x_259);
lean_dec(x_259);
lean_dec(x_278);
x_280 = lean_unsigned_to_nat(0u);
x_281 = l_Lean_Expr_getAppNumArgsAux(x_263, x_280);
x_282 = lean_nat_dec_lt(x_279, x_281);
if (x_282 == 0)
{
lean_dec(x_281);
lean_dec(x_279);
lean_dec(x_263);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_267, 0, x_1);
return x_267;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_free_object(x_267);
lean_dec(x_1);
x_283 = lean_nat_sub(x_281, x_279);
lean_dec(x_279);
lean_dec(x_281);
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_sub(x_283, x_284);
lean_dec(x_283);
x_286 = l_Lean_Expr_getRevArg_x21(x_263, x_285);
lean_dec(x_263);
x_1 = x_286;
x_6 = x_275;
goto _start;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_288 = lean_ctor_get(x_267, 1);
lean_inc(x_288);
lean_dec(x_267);
x_289 = lean_ctor_get(x_273, 0);
lean_inc(x_289);
lean_dec(x_273);
x_290 = lean_ctor_get(x_289, 3);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_nat_add(x_290, x_259);
lean_dec(x_259);
lean_dec(x_290);
x_292 = lean_unsigned_to_nat(0u);
x_293 = l_Lean_Expr_getAppNumArgsAux(x_263, x_292);
x_294 = lean_nat_dec_lt(x_291, x_293);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_263);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_1);
lean_ctor_set(x_295, 1, x_288);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_1);
x_296 = lean_nat_sub(x_293, x_291);
lean_dec(x_291);
lean_dec(x_293);
x_297 = lean_unsigned_to_nat(1u);
x_298 = lean_nat_sub(x_296, x_297);
lean_dec(x_296);
x_299 = l_Lean_Expr_getRevArg_x21(x_263, x_298);
lean_dec(x_263);
x_1 = x_299;
x_6 = x_288;
goto _start;
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_273);
lean_dec(x_263);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_301 = !lean_is_exclusive(x_267);
if (x_301 == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_267, 0);
lean_dec(x_302);
lean_ctor_set(x_267, 0, x_1);
return x_267;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_267, 1);
lean_inc(x_303);
lean_dec(x_267);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_1);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_263);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_267);
if (x_305 == 0)
{
return x_267;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_267, 0);
x_307 = lean_ctor_get(x_267, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_267);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_261, 0, x_1);
return x_261;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_261, 0);
x_310 = lean_ctor_get(x_261, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_261);
x_311 = l_Lean_Expr_getAppFn(x_309);
if (lean_obj_tag(x_311) == 4)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_Lean_Meta_getConst_x3f(x_312, x_2, x_3, x_4, x_5, x_310);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_309);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_316 = x_313;
} else {
 lean_dec_ref(x_313);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
else
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_314, 0);
lean_inc(x_318);
lean_dec(x_314);
if (lean_obj_tag(x_318) == 6)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_320 = x_313;
} else {
 lean_dec_ref(x_313);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
lean_dec(x_318);
x_322 = lean_ctor_get(x_321, 3);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_nat_add(x_322, x_259);
lean_dec(x_259);
lean_dec(x_322);
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Lean_Expr_getAppNumArgsAux(x_309, x_324);
x_326 = lean_nat_dec_lt(x_323, x_325);
if (x_326 == 0)
{
lean_object* x_327; 
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_309);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_320)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_320;
}
lean_ctor_set(x_327, 0, x_1);
lean_ctor_set(x_327, 1, x_319);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_320);
lean_dec(x_1);
x_328 = lean_nat_sub(x_325, x_323);
lean_dec(x_323);
lean_dec(x_325);
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_nat_sub(x_328, x_329);
lean_dec(x_328);
x_331 = l_Lean_Expr_getRevArg_x21(x_309, x_330);
lean_dec(x_309);
x_1 = x_331;
x_6 = x_319;
goto _start;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_318);
lean_dec(x_309);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_333 = lean_ctor_get(x_313, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_334 = x_313;
} else {
 lean_dec_ref(x_313);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_1);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_309);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = lean_ctor_get(x_313, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_313, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_338 = x_313;
} else {
 lean_dec_ref(x_313);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; 
lean_dec(x_311);
lean_dec(x_309);
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_1);
lean_ctor_set(x_340, 1, x_310);
return x_340;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_259);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = !lean_is_exclusive(x_261);
if (x_341 == 0)
{
return x_261;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_261, 0);
x_343 = lean_ctor_get(x_261, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_261);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
default: 
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_1);
x_345 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_346 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
x_347 = lean_panic_fn(x_345, x_346);
x_348 = lean_apply_5(x_347, x_2, x_3, x_4, x_5, x_90);
return x_348;
}
}
}
}
case 5:
{
lean_object* x_365; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
x_625 = lean_st_ref_get(x_5, x_6);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_626, 3);
lean_inc(x_627);
lean_dec(x_626);
x_628 = lean_ctor_get_uint8(x_627, sizeof(void*)*1);
lean_dec(x_627);
if (x_628 == 0)
{
lean_object* x_629; 
x_629 = lean_ctor_get(x_625, 1);
lean_inc(x_629);
lean_dec(x_625);
x_365 = x_629;
goto block_624;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_630 = lean_ctor_get(x_625, 1);
lean_inc(x_630);
lean_dec(x_625);
x_631 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_632 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_631, x_2, x_3, x_4, x_5, x_630);
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_unbox(x_633);
lean_dec(x_633);
if (x_634 == 0)
{
lean_object* x_635; 
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
lean_dec(x_632);
x_365 = x_635;
goto block_624;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_636 = lean_ctor_get(x_632, 1);
lean_inc(x_636);
lean_dec(x_632);
lean_inc(x_1);
x_637 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_637, 0, x_1);
x_638 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_631, x_637, x_2, x_3, x_4, x_5, x_636);
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_365 = x_639;
goto block_624;
}
}
block_624:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_366; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_1);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
case 5:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_1, 0);
lean_inc(x_367);
x_368 = l_Lean_Expr_getAppFn(x_367);
lean_dec(x_367);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_368);
x_369 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_368, x_2, x_3, x_4, x_5, x_365);
if (lean_obj_tag(x_369) == 0)
{
uint8_t x_370; 
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_371 = lean_ctor_get(x_369, 0);
x_372 = lean_ctor_get(x_369, 1);
x_373 = l_Lean_Expr_isLambda(x_371);
if (x_373 == 0)
{
if (lean_obj_tag(x_371) == 4)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_free_object(x_369);
x_374 = lean_ctor_get(x_371, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 1);
lean_inc(x_375);
lean_inc(x_1);
lean_inc(x_371);
lean_inc(x_368);
x_376 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_376, 0, x_368);
lean_closure_set(x_376, 1, x_371);
lean_closure_set(x_376, 2, x_1);
x_377 = l_Lean_Meta_getConst_x3f(x_374, x_2, x_3, x_4, x_5, x_372);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
uint8_t x_379; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_379 = !lean_is_exclusive(x_377);
if (x_379 == 0)
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_377, 0);
lean_dec(x_380);
x_381 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_381 == 0)
{
lean_object* x_382; 
x_382 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
lean_ctor_set(x_377, 0, x_382);
return x_377;
}
else
{
lean_dec(x_371);
lean_ctor_set(x_377, 0, x_1);
return x_377;
}
}
else
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_377, 1);
lean_inc(x_383);
lean_dec(x_377);
x_384 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_383);
return x_386;
}
else
{
lean_object* x_387; 
lean_dec(x_371);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set(x_387, 1, x_383);
return x_387;
}
}
}
else
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_378, 0);
lean_inc(x_388);
lean_dec(x_378);
switch (lean_obj_tag(x_388)) {
case 1:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_376);
x_389 = lean_ctor_get(x_377, 1);
lean_inc(x_389);
lean_dec(x_377);
x_390 = l_Lean_ConstantInfo_name(x_388);
x_391 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_390, x_2, x_3, x_4, x_5, x_389);
lean_dec(x_390);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
uint8_t x_394; 
lean_dec(x_388);
lean_dec(x_375);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_394 = !lean_is_exclusive(x_391);
if (x_394 == 0)
{
lean_object* x_395; uint8_t x_396; 
x_395 = lean_ctor_get(x_391, 0);
lean_dec(x_395);
x_396 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_396 == 0)
{
lean_object* x_397; 
x_397 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
lean_ctor_set(x_391, 0, x_397);
return x_391;
}
else
{
lean_dec(x_371);
lean_ctor_set(x_391, 0, x_1);
return x_391;
}
}
else
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_391, 1);
lean_inc(x_398);
lean_dec(x_391);
x_399 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
x_400 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_398);
return x_401;
}
else
{
lean_object* x_402; 
lean_dec(x_371);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_1);
lean_ctor_set(x_402, 1, x_398);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_403 = lean_ctor_get(x_391, 1);
lean_inc(x_403);
lean_dec(x_391);
x_404 = lean_unsigned_to_nat(0u);
x_405 = l_Lean_Expr_getAppNumArgsAux(x_1, x_404);
x_406 = lean_mk_empty_array_with_capacity(x_405);
lean_dec(x_405);
lean_inc(x_1);
x_407 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_406);
x_408 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_368, x_371, x_388, x_375, x_407, x_2, x_3, x_4, x_5, x_403);
lean_dec(x_407);
lean_dec(x_375);
lean_dec(x_388);
lean_dec(x_371);
lean_dec(x_368);
return x_408;
}
}
case 4:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_371);
lean_dec(x_368);
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
lean_dec(x_377);
x_410 = lean_ctor_get(x_388, 0);
lean_inc(x_410);
lean_dec(x_388);
x_411 = lean_unsigned_to_nat(0u);
x_412 = l_Lean_Expr_getAppNumArgsAux(x_1, x_411);
x_413 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_412);
x_414 = lean_mk_array(x_412, x_413);
x_415 = lean_unsigned_to_nat(1u);
x_416 = lean_nat_sub(x_412, x_415);
lean_dec(x_412);
x_417 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_414, x_416);
x_418 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_419 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_410, x_375, x_417, x_376, x_418, x_2, x_3, x_4, x_5, x_409);
lean_dec(x_417);
lean_dec(x_375);
lean_dec(x_410);
return x_419;
}
case 7:
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_371);
lean_dec(x_368);
x_420 = lean_ctor_get(x_377, 1);
lean_inc(x_420);
lean_dec(x_377);
x_421 = lean_ctor_get(x_388, 0);
lean_inc(x_421);
lean_dec(x_388);
x_422 = lean_unsigned_to_nat(0u);
x_423 = l_Lean_Expr_getAppNumArgsAux(x_1, x_422);
x_424 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_423);
x_425 = lean_mk_array(x_423, x_424);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_nat_sub(x_423, x_426);
lean_dec(x_423);
x_428 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_425, x_427);
x_429 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_430 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_421, x_375, x_428, x_376, x_429, x_2, x_3, x_4, x_5, x_420);
lean_dec(x_428);
lean_dec(x_375);
return x_430;
}
default: 
{
uint8_t x_431; 
lean_dec(x_388);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_431 = !lean_is_exclusive(x_377);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_377, 0);
lean_dec(x_432);
x_433 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
lean_ctor_set(x_377, 0, x_434);
return x_377;
}
else
{
lean_dec(x_371);
lean_ctor_set(x_377, 0, x_1);
return x_377;
}
}
else
{
lean_object* x_435; uint8_t x_436; 
x_435 = lean_ctor_get(x_377, 1);
lean_inc(x_435);
lean_dec(x_377);
x_436 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_435);
return x_438;
}
else
{
lean_object* x_439; 
lean_dec(x_371);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_1);
lean_ctor_set(x_439, 1, x_435);
return x_439;
}
}
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_371);
lean_dec(x_368);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_377);
if (x_440 == 0)
{
return x_377;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_377, 0);
x_442 = lean_ctor_get(x_377, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_377);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_444 = lean_expr_eqv(x_368, x_371);
lean_dec(x_368);
if (x_444 == 0)
{
lean_object* x_445; 
x_445 = l_Lean_Expr_updateFn(x_1, x_371);
lean_dec(x_371);
lean_ctor_set(x_369, 0, x_445);
return x_369;
}
else
{
lean_dec(x_371);
lean_ctor_set(x_369, 0, x_1);
return x_369;
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_free_object(x_369);
lean_dec(x_368);
x_446 = lean_unsigned_to_nat(0u);
x_447 = l_Lean_Expr_getAppNumArgsAux(x_1, x_446);
x_448 = lean_mk_empty_array_with_capacity(x_447);
lean_dec(x_447);
x_449 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_448);
x_450 = l_Lean_Expr_betaRev(x_371, x_449);
lean_dec(x_449);
lean_dec(x_371);
x_1 = x_450;
x_6 = x_372;
goto _start;
}
}
else
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_ctor_get(x_369, 0);
x_453 = lean_ctor_get(x_369, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_369);
x_454 = l_Lean_Expr_isLambda(x_452);
if (x_454 == 0)
{
if (lean_obj_tag(x_452) == 4)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_455 = lean_ctor_get(x_452, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_452, 1);
lean_inc(x_456);
lean_inc(x_1);
lean_inc(x_452);
lean_inc(x_368);
x_457 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_457, 0, x_368);
lean_closure_set(x_457, 1, x_452);
lean_closure_set(x_457, 2, x_1);
x_458 = l_Lean_Meta_getConst_x3f(x_455, x_2, x_3, x_4, x_5, x_453);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_461 = x_458;
} else {
 lean_dec_ref(x_458);
 x_461 = lean_box(0);
}
x_462 = lean_expr_eqv(x_368, x_452);
lean_dec(x_368);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Lean_Expr_updateFn(x_1, x_452);
lean_dec(x_452);
if (lean_is_scalar(x_461)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_461;
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_460);
return x_464;
}
else
{
lean_object* x_465; 
lean_dec(x_452);
if (lean_is_scalar(x_461)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_461;
}
lean_ctor_set(x_465, 0, x_1);
lean_ctor_set(x_465, 1, x_460);
return x_465;
}
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_459, 0);
lean_inc(x_466);
lean_dec(x_459);
switch (lean_obj_tag(x_466)) {
case 1:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
lean_dec(x_457);
x_467 = lean_ctor_get(x_458, 1);
lean_inc(x_467);
lean_dec(x_458);
x_468 = l_Lean_ConstantInfo_name(x_466);
x_469 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_468, x_2, x_3, x_4, x_5, x_467);
lean_dec(x_468);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_unbox(x_470);
lean_dec(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; uint8_t x_474; 
lean_dec(x_466);
lean_dec(x_456);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_472 = lean_ctor_get(x_469, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_473 = x_469;
} else {
 lean_dec_ref(x_469);
 x_473 = lean_box(0);
}
x_474 = lean_expr_eqv(x_368, x_452);
lean_dec(x_368);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = l_Lean_Expr_updateFn(x_1, x_452);
lean_dec(x_452);
if (lean_is_scalar(x_473)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_473;
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_472);
return x_476;
}
else
{
lean_object* x_477; 
lean_dec(x_452);
if (lean_is_scalar(x_473)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_473;
}
lean_ctor_set(x_477, 0, x_1);
lean_ctor_set(x_477, 1, x_472);
return x_477;
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_478 = lean_ctor_get(x_469, 1);
lean_inc(x_478);
lean_dec(x_469);
x_479 = lean_unsigned_to_nat(0u);
x_480 = l_Lean_Expr_getAppNumArgsAux(x_1, x_479);
x_481 = lean_mk_empty_array_with_capacity(x_480);
lean_dec(x_480);
lean_inc(x_1);
x_482 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_481);
x_483 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_368, x_452, x_466, x_456, x_482, x_2, x_3, x_4, x_5, x_478);
lean_dec(x_482);
lean_dec(x_456);
lean_dec(x_466);
lean_dec(x_452);
lean_dec(x_368);
return x_483;
}
}
case 4:
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_452);
lean_dec(x_368);
x_484 = lean_ctor_get(x_458, 1);
lean_inc(x_484);
lean_dec(x_458);
x_485 = lean_ctor_get(x_466, 0);
lean_inc(x_485);
lean_dec(x_466);
x_486 = lean_unsigned_to_nat(0u);
x_487 = l_Lean_Expr_getAppNumArgsAux(x_1, x_486);
x_488 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_487);
x_489 = lean_mk_array(x_487, x_488);
x_490 = lean_unsigned_to_nat(1u);
x_491 = lean_nat_sub(x_487, x_490);
lean_dec(x_487);
x_492 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_489, x_491);
x_493 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_494 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_485, x_456, x_492, x_457, x_493, x_2, x_3, x_4, x_5, x_484);
lean_dec(x_492);
lean_dec(x_456);
lean_dec(x_485);
return x_494;
}
case 7:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_452);
lean_dec(x_368);
x_495 = lean_ctor_get(x_458, 1);
lean_inc(x_495);
lean_dec(x_458);
x_496 = lean_ctor_get(x_466, 0);
lean_inc(x_496);
lean_dec(x_466);
x_497 = lean_unsigned_to_nat(0u);
x_498 = l_Lean_Expr_getAppNumArgsAux(x_1, x_497);
x_499 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_498);
x_500 = lean_mk_array(x_498, x_499);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_nat_sub(x_498, x_501);
lean_dec(x_498);
x_503 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_500, x_502);
x_504 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_505 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_496, x_456, x_503, x_457, x_504, x_2, x_3, x_4, x_5, x_495);
lean_dec(x_503);
lean_dec(x_456);
return x_505;
}
default: 
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
lean_dec(x_466);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_506 = lean_ctor_get(x_458, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_507 = x_458;
} else {
 lean_dec_ref(x_458);
 x_507 = lean_box(0);
}
x_508 = lean_expr_eqv(x_368, x_452);
lean_dec(x_368);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = l_Lean_Expr_updateFn(x_1, x_452);
lean_dec(x_452);
if (lean_is_scalar(x_507)) {
 x_510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_510 = x_507;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_506);
return x_510;
}
else
{
lean_object* x_511; 
lean_dec(x_452);
if (lean_is_scalar(x_507)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_507;
}
lean_ctor_set(x_511, 0, x_1);
lean_ctor_set(x_511, 1, x_506);
return x_511;
}
}
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_452);
lean_dec(x_368);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_458, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_458, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_514 = x_458;
} else {
 lean_dec_ref(x_458);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
uint8_t x_516; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_516 = lean_expr_eqv(x_368, x_452);
lean_dec(x_368);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; 
x_517 = l_Lean_Expr_updateFn(x_1, x_452);
lean_dec(x_452);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_453);
return x_518;
}
else
{
lean_object* x_519; 
lean_dec(x_452);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_1);
lean_ctor_set(x_519, 1, x_453);
return x_519;
}
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_368);
x_520 = lean_unsigned_to_nat(0u);
x_521 = l_Lean_Expr_getAppNumArgsAux(x_1, x_520);
x_522 = lean_mk_empty_array_with_capacity(x_521);
lean_dec(x_521);
x_523 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_522);
x_524 = l_Lean_Expr_betaRev(x_452, x_523);
lean_dec(x_523);
lean_dec(x_452);
x_1 = x_524;
x_6 = x_453;
goto _start;
}
}
}
else
{
uint8_t x_526; 
lean_dec(x_368);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_526 = !lean_is_exclusive(x_369);
if (x_526 == 0)
{
return x_369;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_369, 0);
x_528 = lean_ctor_get(x_369, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_369);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
case 8:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_1, 2);
lean_inc(x_530);
x_531 = lean_ctor_get(x_1, 3);
lean_inc(x_531);
lean_dec(x_1);
x_532 = lean_expr_instantiate1(x_531, x_530);
lean_dec(x_530);
lean_dec(x_531);
x_1 = x_532;
x_6 = x_365;
goto _start;
}
case 11:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_1, 1);
lean_inc(x_534);
x_535 = lean_ctor_get(x_1, 2);
lean_inc(x_535);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_536 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_535, x_2, x_3, x_4, x_5, x_365);
if (lean_obj_tag(x_536) == 0)
{
uint8_t x_537; 
x_537 = !lean_is_exclusive(x_536);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_536, 0);
x_539 = lean_ctor_get(x_536, 1);
x_540 = l_Lean_Expr_getAppFn(x_538);
if (lean_obj_tag(x_540) == 4)
{
lean_object* x_541; lean_object* x_542; 
lean_free_object(x_536);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
lean_dec(x_540);
x_542 = l_Lean_Meta_getConst_x3f(x_541, x_2, x_3, x_4, x_5, x_539);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
if (lean_obj_tag(x_543) == 0)
{
uint8_t x_544; 
lean_dec(x_538);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_544 = !lean_is_exclusive(x_542);
if (x_544 == 0)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_542, 0);
lean_dec(x_545);
lean_ctor_set(x_542, 0, x_1);
return x_542;
}
else
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_542, 1);
lean_inc(x_546);
lean_dec(x_542);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_1);
lean_ctor_set(x_547, 1, x_546);
return x_547;
}
}
else
{
lean_object* x_548; 
x_548 = lean_ctor_get(x_543, 0);
lean_inc(x_548);
lean_dec(x_543);
if (lean_obj_tag(x_548) == 6)
{
uint8_t x_549; 
x_549 = !lean_is_exclusive(x_542);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_550 = lean_ctor_get(x_542, 1);
x_551 = lean_ctor_get(x_542, 0);
lean_dec(x_551);
x_552 = lean_ctor_get(x_548, 0);
lean_inc(x_552);
lean_dec(x_548);
x_553 = lean_ctor_get(x_552, 3);
lean_inc(x_553);
lean_dec(x_552);
x_554 = lean_nat_add(x_553, x_534);
lean_dec(x_534);
lean_dec(x_553);
x_555 = lean_unsigned_to_nat(0u);
x_556 = l_Lean_Expr_getAppNumArgsAux(x_538, x_555);
x_557 = lean_nat_dec_lt(x_554, x_556);
if (x_557 == 0)
{
lean_dec(x_556);
lean_dec(x_554);
lean_dec(x_538);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_542, 0, x_1);
return x_542;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_free_object(x_542);
lean_dec(x_1);
x_558 = lean_nat_sub(x_556, x_554);
lean_dec(x_554);
lean_dec(x_556);
x_559 = lean_unsigned_to_nat(1u);
x_560 = lean_nat_sub(x_558, x_559);
lean_dec(x_558);
x_561 = l_Lean_Expr_getRevArg_x21(x_538, x_560);
lean_dec(x_538);
x_1 = x_561;
x_6 = x_550;
goto _start;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; 
x_563 = lean_ctor_get(x_542, 1);
lean_inc(x_563);
lean_dec(x_542);
x_564 = lean_ctor_get(x_548, 0);
lean_inc(x_564);
lean_dec(x_548);
x_565 = lean_ctor_get(x_564, 3);
lean_inc(x_565);
lean_dec(x_564);
x_566 = lean_nat_add(x_565, x_534);
lean_dec(x_534);
lean_dec(x_565);
x_567 = lean_unsigned_to_nat(0u);
x_568 = l_Lean_Expr_getAppNumArgsAux(x_538, x_567);
x_569 = lean_nat_dec_lt(x_566, x_568);
if (x_569 == 0)
{
lean_object* x_570; 
lean_dec(x_568);
lean_dec(x_566);
lean_dec(x_538);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_1);
lean_ctor_set(x_570, 1, x_563);
return x_570;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_1);
x_571 = lean_nat_sub(x_568, x_566);
lean_dec(x_566);
lean_dec(x_568);
x_572 = lean_unsigned_to_nat(1u);
x_573 = lean_nat_sub(x_571, x_572);
lean_dec(x_571);
x_574 = l_Lean_Expr_getRevArg_x21(x_538, x_573);
lean_dec(x_538);
x_1 = x_574;
x_6 = x_563;
goto _start;
}
}
}
else
{
uint8_t x_576; 
lean_dec(x_548);
lean_dec(x_538);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_576 = !lean_is_exclusive(x_542);
if (x_576 == 0)
{
lean_object* x_577; 
x_577 = lean_ctor_get(x_542, 0);
lean_dec(x_577);
lean_ctor_set(x_542, 0, x_1);
return x_542;
}
else
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_542, 1);
lean_inc(x_578);
lean_dec(x_542);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_1);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
}
else
{
uint8_t x_580; 
lean_dec(x_538);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_580 = !lean_is_exclusive(x_542);
if (x_580 == 0)
{
return x_542;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_542, 0);
x_582 = lean_ctor_get(x_542, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_542);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_dec(x_540);
lean_dec(x_538);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_536, 0, x_1);
return x_536;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_536, 0);
x_585 = lean_ctor_get(x_536, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_536);
x_586 = l_Lean_Expr_getAppFn(x_584);
if (lean_obj_tag(x_586) == 4)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
lean_dec(x_586);
x_588 = l_Lean_Meta_getConst_x3f(x_587, x_2, x_3, x_4, x_5, x_585);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_584);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_591;
}
lean_ctor_set(x_592, 0, x_1);
lean_ctor_set(x_592, 1, x_590);
return x_592;
}
else
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_589, 0);
lean_inc(x_593);
lean_dec(x_589);
if (lean_obj_tag(x_593) == 6)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; 
x_594 = lean_ctor_get(x_588, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_595 = x_588;
} else {
 lean_dec_ref(x_588);
 x_595 = lean_box(0);
}
x_596 = lean_ctor_get(x_593, 0);
lean_inc(x_596);
lean_dec(x_593);
x_597 = lean_ctor_get(x_596, 3);
lean_inc(x_597);
lean_dec(x_596);
x_598 = lean_nat_add(x_597, x_534);
lean_dec(x_534);
lean_dec(x_597);
x_599 = lean_unsigned_to_nat(0u);
x_600 = l_Lean_Expr_getAppNumArgsAux(x_584, x_599);
x_601 = lean_nat_dec_lt(x_598, x_600);
if (x_601 == 0)
{
lean_object* x_602; 
lean_dec(x_600);
lean_dec(x_598);
lean_dec(x_584);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_595)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_595;
}
lean_ctor_set(x_602, 0, x_1);
lean_ctor_set(x_602, 1, x_594);
return x_602;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_595);
lean_dec(x_1);
x_603 = lean_nat_sub(x_600, x_598);
lean_dec(x_598);
lean_dec(x_600);
x_604 = lean_unsigned_to_nat(1u);
x_605 = lean_nat_sub(x_603, x_604);
lean_dec(x_603);
x_606 = l_Lean_Expr_getRevArg_x21(x_584, x_605);
lean_dec(x_584);
x_1 = x_606;
x_6 = x_594;
goto _start;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_593);
lean_dec(x_584);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_608 = lean_ctor_get(x_588, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_609 = x_588;
} else {
 lean_dec_ref(x_588);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_1);
lean_ctor_set(x_610, 1, x_608);
return x_610;
}
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_584);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_611 = lean_ctor_get(x_588, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_588, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_613 = x_588;
} else {
 lean_dec_ref(x_588);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_612);
return x_614;
}
}
else
{
lean_object* x_615; 
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_1);
lean_ctor_set(x_615, 1, x_585);
return x_615;
}
}
}
else
{
uint8_t x_616; 
lean_dec(x_534);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_616 = !lean_is_exclusive(x_536);
if (x_616 == 0)
{
return x_536;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_536, 0);
x_618 = lean_ctor_get(x_536, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_536);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
}
}
default: 
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_1);
x_620 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_621 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
x_622 = lean_panic_fn(x_620, x_621);
x_623 = lean_apply_5(x_622, x_2, x_3, x_4, x_5, x_365);
return x_623;
}
}
}
}
case 8:
{
lean_object* x_640; lean_object* x_900; lean_object* x_901; lean_object* x_902; uint8_t x_903; 
x_900 = lean_st_ref_get(x_5, x_6);
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_901, 3);
lean_inc(x_902);
lean_dec(x_901);
x_903 = lean_ctor_get_uint8(x_902, sizeof(void*)*1);
lean_dec(x_902);
if (x_903 == 0)
{
lean_object* x_904; 
x_904 = lean_ctor_get(x_900, 1);
lean_inc(x_904);
lean_dec(x_900);
x_640 = x_904;
goto block_899;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; uint8_t x_909; 
x_905 = lean_ctor_get(x_900, 1);
lean_inc(x_905);
lean_dec(x_900);
x_906 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_907 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_906, x_2, x_3, x_4, x_5, x_905);
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_unbox(x_908);
lean_dec(x_908);
if (x_909 == 0)
{
lean_object* x_910; 
x_910 = lean_ctor_get(x_907, 1);
lean_inc(x_910);
lean_dec(x_907);
x_640 = x_910;
goto block_899;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_911 = lean_ctor_get(x_907, 1);
lean_inc(x_911);
lean_dec(x_907);
lean_inc(x_1);
x_912 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_912, 0, x_1);
x_913 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_906, x_912, x_2, x_3, x_4, x_5, x_911);
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
lean_dec(x_913);
x_640 = x_914;
goto block_899;
}
}
block_899:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_641; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_1);
lean_ctor_set(x_641, 1, x_640);
return x_641;
}
case 5:
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_1, 0);
lean_inc(x_642);
x_643 = l_Lean_Expr_getAppFn(x_642);
lean_dec(x_642);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_643);
x_644 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_643, x_2, x_3, x_4, x_5, x_640);
if (lean_obj_tag(x_644) == 0)
{
uint8_t x_645; 
x_645 = !lean_is_exclusive(x_644);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; uint8_t x_648; 
x_646 = lean_ctor_get(x_644, 0);
x_647 = lean_ctor_get(x_644, 1);
x_648 = l_Lean_Expr_isLambda(x_646);
if (x_648 == 0)
{
if (lean_obj_tag(x_646) == 4)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_free_object(x_644);
x_649 = lean_ctor_get(x_646, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_646, 1);
lean_inc(x_650);
lean_inc(x_1);
lean_inc(x_646);
lean_inc(x_643);
x_651 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_651, 0, x_643);
lean_closure_set(x_651, 1, x_646);
lean_closure_set(x_651, 2, x_1);
x_652 = l_Lean_Meta_getConst_x3f(x_649, x_2, x_3, x_4, x_5, x_647);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
if (lean_obj_tag(x_653) == 0)
{
uint8_t x_654; 
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_654 = !lean_is_exclusive(x_652);
if (x_654 == 0)
{
lean_object* x_655; uint8_t x_656; 
x_655 = lean_ctor_get(x_652, 0);
lean_dec(x_655);
x_656 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_656 == 0)
{
lean_object* x_657; 
x_657 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
lean_ctor_set(x_652, 0, x_657);
return x_652;
}
else
{
lean_dec(x_646);
lean_ctor_set(x_652, 0, x_1);
return x_652;
}
}
else
{
lean_object* x_658; uint8_t x_659; 
x_658 = lean_ctor_get(x_652, 1);
lean_inc(x_658);
lean_dec(x_652);
x_659 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; 
x_660 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_658);
return x_661;
}
else
{
lean_object* x_662; 
lean_dec(x_646);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_1);
lean_ctor_set(x_662, 1, x_658);
return x_662;
}
}
}
else
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_653, 0);
lean_inc(x_663);
lean_dec(x_653);
switch (lean_obj_tag(x_663)) {
case 1:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
lean_dec(x_651);
x_664 = lean_ctor_get(x_652, 1);
lean_inc(x_664);
lean_dec(x_652);
x_665 = l_Lean_ConstantInfo_name(x_663);
x_666 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_665, x_2, x_3, x_4, x_5, x_664);
lean_dec(x_665);
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_unbox(x_667);
lean_dec(x_667);
if (x_668 == 0)
{
uint8_t x_669; 
lean_dec(x_663);
lean_dec(x_650);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_669 = !lean_is_exclusive(x_666);
if (x_669 == 0)
{
lean_object* x_670; uint8_t x_671; 
x_670 = lean_ctor_get(x_666, 0);
lean_dec(x_670);
x_671 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_671 == 0)
{
lean_object* x_672; 
x_672 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
lean_ctor_set(x_666, 0, x_672);
return x_666;
}
else
{
lean_dec(x_646);
lean_ctor_set(x_666, 0, x_1);
return x_666;
}
}
else
{
lean_object* x_673; uint8_t x_674; 
x_673 = lean_ctor_get(x_666, 1);
lean_inc(x_673);
lean_dec(x_666);
x_674 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_673);
return x_676;
}
else
{
lean_object* x_677; 
lean_dec(x_646);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_1);
lean_ctor_set(x_677, 1, x_673);
return x_677;
}
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_678 = lean_ctor_get(x_666, 1);
lean_inc(x_678);
lean_dec(x_666);
x_679 = lean_unsigned_to_nat(0u);
x_680 = l_Lean_Expr_getAppNumArgsAux(x_1, x_679);
x_681 = lean_mk_empty_array_with_capacity(x_680);
lean_dec(x_680);
lean_inc(x_1);
x_682 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_681);
x_683 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_643, x_646, x_663, x_650, x_682, x_2, x_3, x_4, x_5, x_678);
lean_dec(x_682);
lean_dec(x_650);
lean_dec(x_663);
lean_dec(x_646);
lean_dec(x_643);
return x_683;
}
}
case 4:
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_646);
lean_dec(x_643);
x_684 = lean_ctor_get(x_652, 1);
lean_inc(x_684);
lean_dec(x_652);
x_685 = lean_ctor_get(x_663, 0);
lean_inc(x_685);
lean_dec(x_663);
x_686 = lean_unsigned_to_nat(0u);
x_687 = l_Lean_Expr_getAppNumArgsAux(x_1, x_686);
x_688 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_687);
x_689 = lean_mk_array(x_687, x_688);
x_690 = lean_unsigned_to_nat(1u);
x_691 = lean_nat_sub(x_687, x_690);
lean_dec(x_687);
x_692 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_689, x_691);
x_693 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_694 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_685, x_650, x_692, x_651, x_693, x_2, x_3, x_4, x_5, x_684);
lean_dec(x_692);
lean_dec(x_650);
lean_dec(x_685);
return x_694;
}
case 7:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_646);
lean_dec(x_643);
x_695 = lean_ctor_get(x_652, 1);
lean_inc(x_695);
lean_dec(x_652);
x_696 = lean_ctor_get(x_663, 0);
lean_inc(x_696);
lean_dec(x_663);
x_697 = lean_unsigned_to_nat(0u);
x_698 = l_Lean_Expr_getAppNumArgsAux(x_1, x_697);
x_699 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_698);
x_700 = lean_mk_array(x_698, x_699);
x_701 = lean_unsigned_to_nat(1u);
x_702 = lean_nat_sub(x_698, x_701);
lean_dec(x_698);
x_703 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_700, x_702);
x_704 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_705 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_696, x_650, x_703, x_651, x_704, x_2, x_3, x_4, x_5, x_695);
lean_dec(x_703);
lean_dec(x_650);
return x_705;
}
default: 
{
uint8_t x_706; 
lean_dec(x_663);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_706 = !lean_is_exclusive(x_652);
if (x_706 == 0)
{
lean_object* x_707; uint8_t x_708; 
x_707 = lean_ctor_get(x_652, 0);
lean_dec(x_707);
x_708 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_708 == 0)
{
lean_object* x_709; 
x_709 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
lean_ctor_set(x_652, 0, x_709);
return x_652;
}
else
{
lean_dec(x_646);
lean_ctor_set(x_652, 0, x_1);
return x_652;
}
}
else
{
lean_object* x_710; uint8_t x_711; 
x_710 = lean_ctor_get(x_652, 1);
lean_inc(x_710);
lean_dec(x_652);
x_711 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; 
x_712 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_710);
return x_713;
}
else
{
lean_object* x_714; 
lean_dec(x_646);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_1);
lean_ctor_set(x_714, 1, x_710);
return x_714;
}
}
}
}
}
}
else
{
uint8_t x_715; 
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_646);
lean_dec(x_643);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_715 = !lean_is_exclusive(x_652);
if (x_715 == 0)
{
return x_652;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_652, 0);
x_717 = lean_ctor_get(x_652, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_652);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_719 = lean_expr_eqv(x_643, x_646);
lean_dec(x_643);
if (x_719 == 0)
{
lean_object* x_720; 
x_720 = l_Lean_Expr_updateFn(x_1, x_646);
lean_dec(x_646);
lean_ctor_set(x_644, 0, x_720);
return x_644;
}
else
{
lean_dec(x_646);
lean_ctor_set(x_644, 0, x_1);
return x_644;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_free_object(x_644);
lean_dec(x_643);
x_721 = lean_unsigned_to_nat(0u);
x_722 = l_Lean_Expr_getAppNumArgsAux(x_1, x_721);
x_723 = lean_mk_empty_array_with_capacity(x_722);
lean_dec(x_722);
x_724 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_723);
x_725 = l_Lean_Expr_betaRev(x_646, x_724);
lean_dec(x_724);
lean_dec(x_646);
x_1 = x_725;
x_6 = x_647;
goto _start;
}
}
else
{
lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_727 = lean_ctor_get(x_644, 0);
x_728 = lean_ctor_get(x_644, 1);
lean_inc(x_728);
lean_inc(x_727);
lean_dec(x_644);
x_729 = l_Lean_Expr_isLambda(x_727);
if (x_729 == 0)
{
if (lean_obj_tag(x_727) == 4)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_730 = lean_ctor_get(x_727, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_727, 1);
lean_inc(x_731);
lean_inc(x_1);
lean_inc(x_727);
lean_inc(x_643);
x_732 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_732, 0, x_643);
lean_closure_set(x_732, 1, x_727);
lean_closure_set(x_732, 2, x_1);
x_733 = l_Lean_Meta_getConst_x3f(x_730, x_2, x_3, x_4, x_5, x_728);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; uint8_t x_737; 
lean_dec(x_732);
lean_dec(x_731);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_736 = x_733;
} else {
 lean_dec_ref(x_733);
 x_736 = lean_box(0);
}
x_737 = lean_expr_eqv(x_643, x_727);
lean_dec(x_643);
if (x_737 == 0)
{
lean_object* x_738; lean_object* x_739; 
x_738 = l_Lean_Expr_updateFn(x_1, x_727);
lean_dec(x_727);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_736;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_735);
return x_739;
}
else
{
lean_object* x_740; 
lean_dec(x_727);
if (lean_is_scalar(x_736)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_736;
}
lean_ctor_set(x_740, 0, x_1);
lean_ctor_set(x_740, 1, x_735);
return x_740;
}
}
else
{
lean_object* x_741; 
x_741 = lean_ctor_get(x_734, 0);
lean_inc(x_741);
lean_dec(x_734);
switch (lean_obj_tag(x_741)) {
case 1:
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; 
lean_dec(x_732);
x_742 = lean_ctor_get(x_733, 1);
lean_inc(x_742);
lean_dec(x_733);
x_743 = l_Lean_ConstantInfo_name(x_741);
x_744 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_743, x_2, x_3, x_4, x_5, x_742);
lean_dec(x_743);
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_unbox(x_745);
lean_dec(x_745);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; uint8_t x_749; 
lean_dec(x_741);
lean_dec(x_731);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_747 = lean_ctor_get(x_744, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 x_748 = x_744;
} else {
 lean_dec_ref(x_744);
 x_748 = lean_box(0);
}
x_749 = lean_expr_eqv(x_643, x_727);
lean_dec(x_643);
if (x_749 == 0)
{
lean_object* x_750; lean_object* x_751; 
x_750 = l_Lean_Expr_updateFn(x_1, x_727);
lean_dec(x_727);
if (lean_is_scalar(x_748)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_748;
}
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set(x_751, 1, x_747);
return x_751;
}
else
{
lean_object* x_752; 
lean_dec(x_727);
if (lean_is_scalar(x_748)) {
 x_752 = lean_alloc_ctor(0, 2, 0);
} else {
 x_752 = x_748;
}
lean_ctor_set(x_752, 0, x_1);
lean_ctor_set(x_752, 1, x_747);
return x_752;
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_753 = lean_ctor_get(x_744, 1);
lean_inc(x_753);
lean_dec(x_744);
x_754 = lean_unsigned_to_nat(0u);
x_755 = l_Lean_Expr_getAppNumArgsAux(x_1, x_754);
x_756 = lean_mk_empty_array_with_capacity(x_755);
lean_dec(x_755);
lean_inc(x_1);
x_757 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_756);
x_758 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_643, x_727, x_741, x_731, x_757, x_2, x_3, x_4, x_5, x_753);
lean_dec(x_757);
lean_dec(x_731);
lean_dec(x_741);
lean_dec(x_727);
lean_dec(x_643);
return x_758;
}
}
case 4:
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_727);
lean_dec(x_643);
x_759 = lean_ctor_get(x_733, 1);
lean_inc(x_759);
lean_dec(x_733);
x_760 = lean_ctor_get(x_741, 0);
lean_inc(x_760);
lean_dec(x_741);
x_761 = lean_unsigned_to_nat(0u);
x_762 = l_Lean_Expr_getAppNumArgsAux(x_1, x_761);
x_763 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_762);
x_764 = lean_mk_array(x_762, x_763);
x_765 = lean_unsigned_to_nat(1u);
x_766 = lean_nat_sub(x_762, x_765);
lean_dec(x_762);
x_767 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_764, x_766);
x_768 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_769 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_760, x_731, x_767, x_732, x_768, x_2, x_3, x_4, x_5, x_759);
lean_dec(x_767);
lean_dec(x_731);
lean_dec(x_760);
return x_769;
}
case 7:
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_727);
lean_dec(x_643);
x_770 = lean_ctor_get(x_733, 1);
lean_inc(x_770);
lean_dec(x_733);
x_771 = lean_ctor_get(x_741, 0);
lean_inc(x_771);
lean_dec(x_741);
x_772 = lean_unsigned_to_nat(0u);
x_773 = l_Lean_Expr_getAppNumArgsAux(x_1, x_772);
x_774 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_773);
x_775 = lean_mk_array(x_773, x_774);
x_776 = lean_unsigned_to_nat(1u);
x_777 = lean_nat_sub(x_773, x_776);
lean_dec(x_773);
x_778 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_775, x_777);
x_779 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_780 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_771, x_731, x_778, x_732, x_779, x_2, x_3, x_4, x_5, x_770);
lean_dec(x_778);
lean_dec(x_731);
return x_780;
}
default: 
{
lean_object* x_781; lean_object* x_782; uint8_t x_783; 
lean_dec(x_741);
lean_dec(x_732);
lean_dec(x_731);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_781 = lean_ctor_get(x_733, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_782 = x_733;
} else {
 lean_dec_ref(x_733);
 x_782 = lean_box(0);
}
x_783 = lean_expr_eqv(x_643, x_727);
lean_dec(x_643);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; 
x_784 = l_Lean_Expr_updateFn(x_1, x_727);
lean_dec(x_727);
if (lean_is_scalar(x_782)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_782;
}
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_781);
return x_785;
}
else
{
lean_object* x_786; 
lean_dec(x_727);
if (lean_is_scalar(x_782)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_782;
}
lean_ctor_set(x_786, 0, x_1);
lean_ctor_set(x_786, 1, x_781);
return x_786;
}
}
}
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_732);
lean_dec(x_731);
lean_dec(x_727);
lean_dec(x_643);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_787 = lean_ctor_get(x_733, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_733, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_789 = x_733;
} else {
 lean_dec_ref(x_733);
 x_789 = lean_box(0);
}
if (lean_is_scalar(x_789)) {
 x_790 = lean_alloc_ctor(1, 2, 0);
} else {
 x_790 = x_789;
}
lean_ctor_set(x_790, 0, x_787);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
}
else
{
uint8_t x_791; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_791 = lean_expr_eqv(x_643, x_727);
lean_dec(x_643);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; 
x_792 = l_Lean_Expr_updateFn(x_1, x_727);
lean_dec(x_727);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_728);
return x_793;
}
else
{
lean_object* x_794; 
lean_dec(x_727);
x_794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_794, 0, x_1);
lean_ctor_set(x_794, 1, x_728);
return x_794;
}
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_643);
x_795 = lean_unsigned_to_nat(0u);
x_796 = l_Lean_Expr_getAppNumArgsAux(x_1, x_795);
x_797 = lean_mk_empty_array_with_capacity(x_796);
lean_dec(x_796);
x_798 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_797);
x_799 = l_Lean_Expr_betaRev(x_727, x_798);
lean_dec(x_798);
lean_dec(x_727);
x_1 = x_799;
x_6 = x_728;
goto _start;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_643);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_801 = !lean_is_exclusive(x_644);
if (x_801 == 0)
{
return x_644;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_644, 0);
x_803 = lean_ctor_get(x_644, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_644);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
case 8:
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_1, 2);
lean_inc(x_805);
x_806 = lean_ctor_get(x_1, 3);
lean_inc(x_806);
lean_dec(x_1);
x_807 = lean_expr_instantiate1(x_806, x_805);
lean_dec(x_805);
lean_dec(x_806);
x_1 = x_807;
x_6 = x_640;
goto _start;
}
case 11:
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_1, 1);
lean_inc(x_809);
x_810 = lean_ctor_get(x_1, 2);
lean_inc(x_810);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_811 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_810, x_2, x_3, x_4, x_5, x_640);
if (lean_obj_tag(x_811) == 0)
{
uint8_t x_812; 
x_812 = !lean_is_exclusive(x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_811, 0);
x_814 = lean_ctor_get(x_811, 1);
x_815 = l_Lean_Expr_getAppFn(x_813);
if (lean_obj_tag(x_815) == 4)
{
lean_object* x_816; lean_object* x_817; 
lean_free_object(x_811);
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
lean_dec(x_815);
x_817 = l_Lean_Meta_getConst_x3f(x_816, x_2, x_3, x_4, x_5, x_814);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
if (lean_obj_tag(x_818) == 0)
{
uint8_t x_819; 
lean_dec(x_813);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_819 = !lean_is_exclusive(x_817);
if (x_819 == 0)
{
lean_object* x_820; 
x_820 = lean_ctor_get(x_817, 0);
lean_dec(x_820);
lean_ctor_set(x_817, 0, x_1);
return x_817;
}
else
{
lean_object* x_821; lean_object* x_822; 
x_821 = lean_ctor_get(x_817, 1);
lean_inc(x_821);
lean_dec(x_817);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_1);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
else
{
lean_object* x_823; 
x_823 = lean_ctor_get(x_818, 0);
lean_inc(x_823);
lean_dec(x_818);
if (lean_obj_tag(x_823) == 6)
{
uint8_t x_824; 
x_824 = !lean_is_exclusive(x_817);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_825 = lean_ctor_get(x_817, 1);
x_826 = lean_ctor_get(x_817, 0);
lean_dec(x_826);
x_827 = lean_ctor_get(x_823, 0);
lean_inc(x_827);
lean_dec(x_823);
x_828 = lean_ctor_get(x_827, 3);
lean_inc(x_828);
lean_dec(x_827);
x_829 = lean_nat_add(x_828, x_809);
lean_dec(x_809);
lean_dec(x_828);
x_830 = lean_unsigned_to_nat(0u);
x_831 = l_Lean_Expr_getAppNumArgsAux(x_813, x_830);
x_832 = lean_nat_dec_lt(x_829, x_831);
if (x_832 == 0)
{
lean_dec(x_831);
lean_dec(x_829);
lean_dec(x_813);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_817, 0, x_1);
return x_817;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_free_object(x_817);
lean_dec(x_1);
x_833 = lean_nat_sub(x_831, x_829);
lean_dec(x_829);
lean_dec(x_831);
x_834 = lean_unsigned_to_nat(1u);
x_835 = lean_nat_sub(x_833, x_834);
lean_dec(x_833);
x_836 = l_Lean_Expr_getRevArg_x21(x_813, x_835);
lean_dec(x_813);
x_1 = x_836;
x_6 = x_825;
goto _start;
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; 
x_838 = lean_ctor_get(x_817, 1);
lean_inc(x_838);
lean_dec(x_817);
x_839 = lean_ctor_get(x_823, 0);
lean_inc(x_839);
lean_dec(x_823);
x_840 = lean_ctor_get(x_839, 3);
lean_inc(x_840);
lean_dec(x_839);
x_841 = lean_nat_add(x_840, x_809);
lean_dec(x_809);
lean_dec(x_840);
x_842 = lean_unsigned_to_nat(0u);
x_843 = l_Lean_Expr_getAppNumArgsAux(x_813, x_842);
x_844 = lean_nat_dec_lt(x_841, x_843);
if (x_844 == 0)
{
lean_object* x_845; 
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_813);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_845 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_845, 0, x_1);
lean_ctor_set(x_845, 1, x_838);
return x_845;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_1);
x_846 = lean_nat_sub(x_843, x_841);
lean_dec(x_841);
lean_dec(x_843);
x_847 = lean_unsigned_to_nat(1u);
x_848 = lean_nat_sub(x_846, x_847);
lean_dec(x_846);
x_849 = l_Lean_Expr_getRevArg_x21(x_813, x_848);
lean_dec(x_813);
x_1 = x_849;
x_6 = x_838;
goto _start;
}
}
}
else
{
uint8_t x_851; 
lean_dec(x_823);
lean_dec(x_813);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_851 = !lean_is_exclusive(x_817);
if (x_851 == 0)
{
lean_object* x_852; 
x_852 = lean_ctor_get(x_817, 0);
lean_dec(x_852);
lean_ctor_set(x_817, 0, x_1);
return x_817;
}
else
{
lean_object* x_853; lean_object* x_854; 
x_853 = lean_ctor_get(x_817, 1);
lean_inc(x_853);
lean_dec(x_817);
x_854 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_854, 0, x_1);
lean_ctor_set(x_854, 1, x_853);
return x_854;
}
}
}
}
else
{
uint8_t x_855; 
lean_dec(x_813);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_855 = !lean_is_exclusive(x_817);
if (x_855 == 0)
{
return x_817;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_856 = lean_ctor_get(x_817, 0);
x_857 = lean_ctor_get(x_817, 1);
lean_inc(x_857);
lean_inc(x_856);
lean_dec(x_817);
x_858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_858, 0, x_856);
lean_ctor_set(x_858, 1, x_857);
return x_858;
}
}
}
else
{
lean_dec(x_815);
lean_dec(x_813);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_811, 0, x_1);
return x_811;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_859 = lean_ctor_get(x_811, 0);
x_860 = lean_ctor_get(x_811, 1);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_811);
x_861 = l_Lean_Expr_getAppFn(x_859);
if (lean_obj_tag(x_861) == 4)
{
lean_object* x_862; lean_object* x_863; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
lean_dec(x_861);
x_863 = l_Lean_Meta_getConst_x3f(x_862, x_2, x_3, x_4, x_5, x_860);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_859);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_866 = x_863;
} else {
 lean_dec_ref(x_863);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_1);
lean_ctor_set(x_867, 1, x_865);
return x_867;
}
else
{
lean_object* x_868; 
x_868 = lean_ctor_get(x_864, 0);
lean_inc(x_868);
lean_dec(x_864);
if (lean_obj_tag(x_868) == 6)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; uint8_t x_876; 
x_869 = lean_ctor_get(x_863, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_870 = x_863;
} else {
 lean_dec_ref(x_863);
 x_870 = lean_box(0);
}
x_871 = lean_ctor_get(x_868, 0);
lean_inc(x_871);
lean_dec(x_868);
x_872 = lean_ctor_get(x_871, 3);
lean_inc(x_872);
lean_dec(x_871);
x_873 = lean_nat_add(x_872, x_809);
lean_dec(x_809);
lean_dec(x_872);
x_874 = lean_unsigned_to_nat(0u);
x_875 = l_Lean_Expr_getAppNumArgsAux(x_859, x_874);
x_876 = lean_nat_dec_lt(x_873, x_875);
if (x_876 == 0)
{
lean_object* x_877; 
lean_dec(x_875);
lean_dec(x_873);
lean_dec(x_859);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_870)) {
 x_877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_877 = x_870;
}
lean_ctor_set(x_877, 0, x_1);
lean_ctor_set(x_877, 1, x_869);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_870);
lean_dec(x_1);
x_878 = lean_nat_sub(x_875, x_873);
lean_dec(x_873);
lean_dec(x_875);
x_879 = lean_unsigned_to_nat(1u);
x_880 = lean_nat_sub(x_878, x_879);
lean_dec(x_878);
x_881 = l_Lean_Expr_getRevArg_x21(x_859, x_880);
lean_dec(x_859);
x_1 = x_881;
x_6 = x_869;
goto _start;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_868);
lean_dec(x_859);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_883 = lean_ctor_get(x_863, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_884 = x_863;
} else {
 lean_dec_ref(x_863);
 x_884 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_885 = lean_alloc_ctor(0, 2, 0);
} else {
 x_885 = x_884;
}
lean_ctor_set(x_885, 0, x_1);
lean_ctor_set(x_885, 1, x_883);
return x_885;
}
}
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_859);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_886 = lean_ctor_get(x_863, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_863, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_888 = x_863;
} else {
 lean_dec_ref(x_863);
 x_888 = lean_box(0);
}
if (lean_is_scalar(x_888)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_888;
}
lean_ctor_set(x_889, 0, x_886);
lean_ctor_set(x_889, 1, x_887);
return x_889;
}
}
else
{
lean_object* x_890; 
lean_dec(x_861);
lean_dec(x_859);
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_890 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_890, 0, x_1);
lean_ctor_set(x_890, 1, x_860);
return x_890;
}
}
}
else
{
uint8_t x_891; 
lean_dec(x_809);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_891 = !lean_is_exclusive(x_811);
if (x_891 == 0)
{
return x_811;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_811, 0);
x_893 = lean_ctor_get(x_811, 1);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_811);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
return x_894;
}
}
}
default: 
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_1);
x_895 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_896 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
x_897 = lean_panic_fn(x_895, x_896);
x_898 = lean_apply_5(x_897, x_2, x_3, x_4, x_5, x_640);
return x_898;
}
}
}
}
case 10:
{
lean_object* x_915; 
x_915 = lean_ctor_get(x_1, 1);
lean_inc(x_915);
lean_dec(x_1);
x_1 = x_915;
goto _start;
}
case 11:
{
lean_object* x_917; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; 
x_1177 = lean_st_ref_get(x_5, x_6);
x_1178 = lean_ctor_get(x_1177, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1178, 3);
lean_inc(x_1179);
lean_dec(x_1178);
x_1180 = lean_ctor_get_uint8(x_1179, sizeof(void*)*1);
lean_dec(x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; 
x_1181 = lean_ctor_get(x_1177, 1);
lean_inc(x_1181);
lean_dec(x_1177);
x_917 = x_1181;
goto block_1176;
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
x_1182 = lean_ctor_get(x_1177, 1);
lean_inc(x_1182);
lean_dec(x_1177);
x_1183 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_1184 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_1183, x_2, x_3, x_4, x_5, x_1182);
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
x_1186 = lean_unbox(x_1185);
lean_dec(x_1185);
if (x_1186 == 0)
{
lean_object* x_1187; 
x_1187 = lean_ctor_get(x_1184, 1);
lean_inc(x_1187);
lean_dec(x_1184);
x_917 = x_1187;
goto block_1176;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1188 = lean_ctor_get(x_1184, 1);
lean_inc(x_1188);
lean_dec(x_1184);
lean_inc(x_1);
x_1189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1189, 0, x_1);
x_1190 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_1183, x_1189, x_2, x_3, x_4, x_5, x_1188);
x_1191 = lean_ctor_get(x_1190, 1);
lean_inc(x_1191);
lean_dec(x_1190);
x_917 = x_1191;
goto block_1176;
}
}
block_1176:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_918; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_918 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_918, 0, x_1);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
case 5:
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_1, 0);
lean_inc(x_919);
x_920 = l_Lean_Expr_getAppFn(x_919);
lean_dec(x_919);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_920);
x_921 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_920, x_2, x_3, x_4, x_5, x_917);
if (lean_obj_tag(x_921) == 0)
{
uint8_t x_922; 
x_922 = !lean_is_exclusive(x_921);
if (x_922 == 0)
{
lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_923 = lean_ctor_get(x_921, 0);
x_924 = lean_ctor_get(x_921, 1);
x_925 = l_Lean_Expr_isLambda(x_923);
if (x_925 == 0)
{
if (lean_obj_tag(x_923) == 4)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_free_object(x_921);
x_926 = lean_ctor_get(x_923, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_923, 1);
lean_inc(x_927);
lean_inc(x_1);
lean_inc(x_923);
lean_inc(x_920);
x_928 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_928, 0, x_920);
lean_closure_set(x_928, 1, x_923);
lean_closure_set(x_928, 2, x_1);
x_929 = l_Lean_Meta_getConst_x3f(x_926, x_2, x_3, x_4, x_5, x_924);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
if (lean_obj_tag(x_930) == 0)
{
uint8_t x_931; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_931 = !lean_is_exclusive(x_929);
if (x_931 == 0)
{
lean_object* x_932; uint8_t x_933; 
x_932 = lean_ctor_get(x_929, 0);
lean_dec(x_932);
x_933 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_933 == 0)
{
lean_object* x_934; 
x_934 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
lean_ctor_set(x_929, 0, x_934);
return x_929;
}
else
{
lean_dec(x_923);
lean_ctor_set(x_929, 0, x_1);
return x_929;
}
}
else
{
lean_object* x_935; uint8_t x_936; 
x_935 = lean_ctor_get(x_929, 1);
lean_inc(x_935);
lean_dec(x_929);
x_936 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_936 == 0)
{
lean_object* x_937; lean_object* x_938; 
x_937 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
x_938 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_935);
return x_938;
}
else
{
lean_object* x_939; 
lean_dec(x_923);
x_939 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_939, 0, x_1);
lean_ctor_set(x_939, 1, x_935);
return x_939;
}
}
}
else
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_930, 0);
lean_inc(x_940);
lean_dec(x_930);
switch (lean_obj_tag(x_940)) {
case 1:
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; uint8_t x_945; 
lean_dec(x_928);
x_941 = lean_ctor_get(x_929, 1);
lean_inc(x_941);
lean_dec(x_929);
x_942 = l_Lean_ConstantInfo_name(x_940);
x_943 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_942, x_2, x_3, x_4, x_5, x_941);
lean_dec(x_942);
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
x_945 = lean_unbox(x_944);
lean_dec(x_944);
if (x_945 == 0)
{
uint8_t x_946; 
lean_dec(x_940);
lean_dec(x_927);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_946 = !lean_is_exclusive(x_943);
if (x_946 == 0)
{
lean_object* x_947; uint8_t x_948; 
x_947 = lean_ctor_get(x_943, 0);
lean_dec(x_947);
x_948 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_948 == 0)
{
lean_object* x_949; 
x_949 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
lean_ctor_set(x_943, 0, x_949);
return x_943;
}
else
{
lean_dec(x_923);
lean_ctor_set(x_943, 0, x_1);
return x_943;
}
}
else
{
lean_object* x_950; uint8_t x_951; 
x_950 = lean_ctor_get(x_943, 1);
lean_inc(x_950);
lean_dec(x_943);
x_951 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_951 == 0)
{
lean_object* x_952; lean_object* x_953; 
x_952 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
x_953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_950);
return x_953;
}
else
{
lean_object* x_954; 
lean_dec(x_923);
x_954 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_954, 0, x_1);
lean_ctor_set(x_954, 1, x_950);
return x_954;
}
}
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_955 = lean_ctor_get(x_943, 1);
lean_inc(x_955);
lean_dec(x_943);
x_956 = lean_unsigned_to_nat(0u);
x_957 = l_Lean_Expr_getAppNumArgsAux(x_1, x_956);
x_958 = lean_mk_empty_array_with_capacity(x_957);
lean_dec(x_957);
lean_inc(x_1);
x_959 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_958);
x_960 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_920, x_923, x_940, x_927, x_959, x_2, x_3, x_4, x_5, x_955);
lean_dec(x_959);
lean_dec(x_927);
lean_dec(x_940);
lean_dec(x_923);
lean_dec(x_920);
return x_960;
}
}
case 4:
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_923);
lean_dec(x_920);
x_961 = lean_ctor_get(x_929, 1);
lean_inc(x_961);
lean_dec(x_929);
x_962 = lean_ctor_get(x_940, 0);
lean_inc(x_962);
lean_dec(x_940);
x_963 = lean_unsigned_to_nat(0u);
x_964 = l_Lean_Expr_getAppNumArgsAux(x_1, x_963);
x_965 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_964);
x_966 = lean_mk_array(x_964, x_965);
x_967 = lean_unsigned_to_nat(1u);
x_968 = lean_nat_sub(x_964, x_967);
lean_dec(x_964);
x_969 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_966, x_968);
x_970 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_971 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_962, x_927, x_969, x_928, x_970, x_2, x_3, x_4, x_5, x_961);
lean_dec(x_969);
lean_dec(x_927);
lean_dec(x_962);
return x_971;
}
case 7:
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
lean_dec(x_923);
lean_dec(x_920);
x_972 = lean_ctor_get(x_929, 1);
lean_inc(x_972);
lean_dec(x_929);
x_973 = lean_ctor_get(x_940, 0);
lean_inc(x_973);
lean_dec(x_940);
x_974 = lean_unsigned_to_nat(0u);
x_975 = l_Lean_Expr_getAppNumArgsAux(x_1, x_974);
x_976 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_975);
x_977 = lean_mk_array(x_975, x_976);
x_978 = lean_unsigned_to_nat(1u);
x_979 = lean_nat_sub(x_975, x_978);
lean_dec(x_975);
x_980 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_977, x_979);
x_981 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_982 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_973, x_927, x_980, x_928, x_981, x_2, x_3, x_4, x_5, x_972);
lean_dec(x_980);
lean_dec(x_927);
return x_982;
}
default: 
{
uint8_t x_983; 
lean_dec(x_940);
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_983 = !lean_is_exclusive(x_929);
if (x_983 == 0)
{
lean_object* x_984; uint8_t x_985; 
x_984 = lean_ctor_get(x_929, 0);
lean_dec(x_984);
x_985 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_985 == 0)
{
lean_object* x_986; 
x_986 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
lean_ctor_set(x_929, 0, x_986);
return x_929;
}
else
{
lean_dec(x_923);
lean_ctor_set(x_929, 0, x_1);
return x_929;
}
}
else
{
lean_object* x_987; uint8_t x_988; 
x_987 = lean_ctor_get(x_929, 1);
lean_inc(x_987);
lean_dec(x_929);
x_988 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; 
x_989 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
x_990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_990, 1, x_987);
return x_990;
}
else
{
lean_object* x_991; 
lean_dec(x_923);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_1);
lean_ctor_set(x_991, 1, x_987);
return x_991;
}
}
}
}
}
}
else
{
uint8_t x_992; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_992 = !lean_is_exclusive(x_929);
if (x_992 == 0)
{
return x_929;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_929, 0);
x_994 = lean_ctor_get(x_929, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_929);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
return x_995;
}
}
}
else
{
uint8_t x_996; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_996 = lean_expr_eqv(x_920, x_923);
lean_dec(x_920);
if (x_996 == 0)
{
lean_object* x_997; 
x_997 = l_Lean_Expr_updateFn(x_1, x_923);
lean_dec(x_923);
lean_ctor_set(x_921, 0, x_997);
return x_921;
}
else
{
lean_dec(x_923);
lean_ctor_set(x_921, 0, x_1);
return x_921;
}
}
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_free_object(x_921);
lean_dec(x_920);
x_998 = lean_unsigned_to_nat(0u);
x_999 = l_Lean_Expr_getAppNumArgsAux(x_1, x_998);
x_1000 = lean_mk_empty_array_with_capacity(x_999);
lean_dec(x_999);
x_1001 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_1000);
x_1002 = l_Lean_Expr_betaRev(x_923, x_1001);
lean_dec(x_1001);
lean_dec(x_923);
x_1 = x_1002;
x_6 = x_924;
goto _start;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; uint8_t x_1006; 
x_1004 = lean_ctor_get(x_921, 0);
x_1005 = lean_ctor_get(x_921, 1);
lean_inc(x_1005);
lean_inc(x_1004);
lean_dec(x_921);
x_1006 = l_Lean_Expr_isLambda(x_1004);
if (x_1006 == 0)
{
if (lean_obj_tag(x_1004) == 4)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1007 = lean_ctor_get(x_1004, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1004, 1);
lean_inc(x_1008);
lean_inc(x_1);
lean_inc(x_1004);
lean_inc(x_920);
x_1009 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_1009, 0, x_920);
lean_closure_set(x_1009, 1, x_1004);
lean_closure_set(x_1009, 2, x_1);
x_1010 = l_Lean_Meta_getConst_x3f(x_1007, x_2, x_3, x_4, x_5, x_1005);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1013 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1013 = lean_box(0);
}
x_1014 = lean_expr_eqv(x_920, x_1004);
lean_dec(x_920);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; 
x_1015 = l_Lean_Expr_updateFn(x_1, x_1004);
lean_dec(x_1004);
if (lean_is_scalar(x_1013)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_1013;
}
lean_ctor_set(x_1016, 0, x_1015);
lean_ctor_set(x_1016, 1, x_1012);
return x_1016;
}
else
{
lean_object* x_1017; 
lean_dec(x_1004);
if (lean_is_scalar(x_1013)) {
 x_1017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1017 = x_1013;
}
lean_ctor_set(x_1017, 0, x_1);
lean_ctor_set(x_1017, 1, x_1012);
return x_1017;
}
}
else
{
lean_object* x_1018; 
x_1018 = lean_ctor_get(x_1011, 0);
lean_inc(x_1018);
lean_dec(x_1011);
switch (lean_obj_tag(x_1018)) {
case 1:
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; uint8_t x_1023; 
lean_dec(x_1009);
x_1019 = lean_ctor_get(x_1010, 1);
lean_inc(x_1019);
lean_dec(x_1010);
x_1020 = l_Lean_ConstantInfo_name(x_1018);
x_1021 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_1020, x_2, x_3, x_4, x_5, x_1019);
lean_dec(x_1020);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_unbox(x_1022);
lean_dec(x_1022);
if (x_1023 == 0)
{
lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
lean_dec(x_1018);
lean_dec(x_1008);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1024 = lean_ctor_get(x_1021, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1025 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1025 = lean_box(0);
}
x_1026 = lean_expr_eqv(x_920, x_1004);
lean_dec(x_920);
if (x_1026 == 0)
{
lean_object* x_1027; lean_object* x_1028; 
x_1027 = l_Lean_Expr_updateFn(x_1, x_1004);
lean_dec(x_1004);
if (lean_is_scalar(x_1025)) {
 x_1028 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1028 = x_1025;
}
lean_ctor_set(x_1028, 0, x_1027);
lean_ctor_set(x_1028, 1, x_1024);
return x_1028;
}
else
{
lean_object* x_1029; 
lean_dec(x_1004);
if (lean_is_scalar(x_1025)) {
 x_1029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1029 = x_1025;
}
lean_ctor_set(x_1029, 0, x_1);
lean_ctor_set(x_1029, 1, x_1024);
return x_1029;
}
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1030 = lean_ctor_get(x_1021, 1);
lean_inc(x_1030);
lean_dec(x_1021);
x_1031 = lean_unsigned_to_nat(0u);
x_1032 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1031);
x_1033 = lean_mk_empty_array_with_capacity(x_1032);
lean_dec(x_1032);
lean_inc(x_1);
x_1034 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_1033);
x_1035 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_920, x_1004, x_1018, x_1008, x_1034, x_2, x_3, x_4, x_5, x_1030);
lean_dec(x_1034);
lean_dec(x_1008);
lean_dec(x_1018);
lean_dec(x_1004);
lean_dec(x_920);
return x_1035;
}
}
case 4:
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_1004);
lean_dec(x_920);
x_1036 = lean_ctor_get(x_1010, 1);
lean_inc(x_1036);
lean_dec(x_1010);
x_1037 = lean_ctor_get(x_1018, 0);
lean_inc(x_1037);
lean_dec(x_1018);
x_1038 = lean_unsigned_to_nat(0u);
x_1039 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1038);
x_1040 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1039);
x_1041 = lean_mk_array(x_1039, x_1040);
x_1042 = lean_unsigned_to_nat(1u);
x_1043 = lean_nat_sub(x_1039, x_1042);
lean_dec(x_1039);
x_1044 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_1041, x_1043);
x_1045 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_1046 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_1037, x_1008, x_1044, x_1009, x_1045, x_2, x_3, x_4, x_5, x_1036);
lean_dec(x_1044);
lean_dec(x_1008);
lean_dec(x_1037);
return x_1046;
}
case 7:
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_1004);
lean_dec(x_920);
x_1047 = lean_ctor_get(x_1010, 1);
lean_inc(x_1047);
lean_dec(x_1010);
x_1048 = lean_ctor_get(x_1018, 0);
lean_inc(x_1048);
lean_dec(x_1018);
x_1049 = lean_unsigned_to_nat(0u);
x_1050 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1049);
x_1051 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1050);
x_1052 = lean_mk_array(x_1050, x_1051);
x_1053 = lean_unsigned_to_nat(1u);
x_1054 = lean_nat_sub(x_1050, x_1053);
lean_dec(x_1050);
x_1055 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_1052, x_1054);
x_1056 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_1057 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_1048, x_1008, x_1055, x_1009, x_1056, x_2, x_3, x_4, x_5, x_1047);
lean_dec(x_1055);
lean_dec(x_1008);
return x_1057;
}
default: 
{
lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; 
lean_dec(x_1018);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1058 = lean_ctor_get(x_1010, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1059 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1059 = lean_box(0);
}
x_1060 = lean_expr_eqv(x_920, x_1004);
lean_dec(x_920);
if (x_1060 == 0)
{
lean_object* x_1061; lean_object* x_1062; 
x_1061 = l_Lean_Expr_updateFn(x_1, x_1004);
lean_dec(x_1004);
if (lean_is_scalar(x_1059)) {
 x_1062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1062 = x_1059;
}
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1058);
return x_1062;
}
else
{
lean_object* x_1063; 
lean_dec(x_1004);
if (lean_is_scalar(x_1059)) {
 x_1063 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1063 = x_1059;
}
lean_ctor_set(x_1063, 0, x_1);
lean_ctor_set(x_1063, 1, x_1058);
return x_1063;
}
}
}
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1004);
lean_dec(x_920);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1064 = lean_ctor_get(x_1010, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1010, 1);
lean_inc(x_1065);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1066 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1066 = lean_box(0);
}
if (lean_is_scalar(x_1066)) {
 x_1067 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1067 = x_1066;
}
lean_ctor_set(x_1067, 0, x_1064);
lean_ctor_set(x_1067, 1, x_1065);
return x_1067;
}
}
else
{
uint8_t x_1068; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1068 = lean_expr_eqv(x_920, x_1004);
lean_dec(x_920);
if (x_1068 == 0)
{
lean_object* x_1069; lean_object* x_1070; 
x_1069 = l_Lean_Expr_updateFn(x_1, x_1004);
lean_dec(x_1004);
x_1070 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1005);
return x_1070;
}
else
{
lean_object* x_1071; 
lean_dec(x_1004);
x_1071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1071, 0, x_1);
lean_ctor_set(x_1071, 1, x_1005);
return x_1071;
}
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_920);
x_1072 = lean_unsigned_to_nat(0u);
x_1073 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1072);
x_1074 = lean_mk_empty_array_with_capacity(x_1073);
lean_dec(x_1073);
x_1075 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_1074);
x_1076 = l_Lean_Expr_betaRev(x_1004, x_1075);
lean_dec(x_1075);
lean_dec(x_1004);
x_1 = x_1076;
x_6 = x_1005;
goto _start;
}
}
}
else
{
uint8_t x_1078; 
lean_dec(x_920);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1078 = !lean_is_exclusive(x_921);
if (x_1078 == 0)
{
return x_921;
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1079 = lean_ctor_get(x_921, 0);
x_1080 = lean_ctor_get(x_921, 1);
lean_inc(x_1080);
lean_inc(x_1079);
lean_dec(x_921);
x_1081 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1081, 0, x_1079);
lean_ctor_set(x_1081, 1, x_1080);
return x_1081;
}
}
}
case 8:
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1082 = lean_ctor_get(x_1, 2);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1, 3);
lean_inc(x_1083);
lean_dec(x_1);
x_1084 = lean_expr_instantiate1(x_1083, x_1082);
lean_dec(x_1082);
lean_dec(x_1083);
x_1 = x_1084;
x_6 = x_917;
goto _start;
}
case 11:
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1086 = lean_ctor_get(x_1, 1);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1, 2);
lean_inc(x_1087);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1088 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_1087, x_2, x_3, x_4, x_5, x_917);
if (lean_obj_tag(x_1088) == 0)
{
uint8_t x_1089; 
x_1089 = !lean_is_exclusive(x_1088);
if (x_1089 == 0)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_1088, 0);
x_1091 = lean_ctor_get(x_1088, 1);
x_1092 = l_Lean_Expr_getAppFn(x_1090);
if (lean_obj_tag(x_1092) == 4)
{
lean_object* x_1093; lean_object* x_1094; 
lean_free_object(x_1088);
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
lean_dec(x_1092);
x_1094 = l_Lean_Meta_getConst_x3f(x_1093, x_2, x_3, x_4, x_5, x_1091);
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; 
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
if (lean_obj_tag(x_1095) == 0)
{
uint8_t x_1096; 
lean_dec(x_1090);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1096 = !lean_is_exclusive(x_1094);
if (x_1096 == 0)
{
lean_object* x_1097; 
x_1097 = lean_ctor_get(x_1094, 0);
lean_dec(x_1097);
lean_ctor_set(x_1094, 0, x_1);
return x_1094;
}
else
{
lean_object* x_1098; lean_object* x_1099; 
x_1098 = lean_ctor_get(x_1094, 1);
lean_inc(x_1098);
lean_dec(x_1094);
x_1099 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1099, 0, x_1);
lean_ctor_set(x_1099, 1, x_1098);
return x_1099;
}
}
else
{
lean_object* x_1100; 
x_1100 = lean_ctor_get(x_1095, 0);
lean_inc(x_1100);
lean_dec(x_1095);
if (lean_obj_tag(x_1100) == 6)
{
uint8_t x_1101; 
x_1101 = !lean_is_exclusive(x_1094);
if (x_1101 == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; 
x_1102 = lean_ctor_get(x_1094, 1);
x_1103 = lean_ctor_get(x_1094, 0);
lean_dec(x_1103);
x_1104 = lean_ctor_get(x_1100, 0);
lean_inc(x_1104);
lean_dec(x_1100);
x_1105 = lean_ctor_get(x_1104, 3);
lean_inc(x_1105);
lean_dec(x_1104);
x_1106 = lean_nat_add(x_1105, x_1086);
lean_dec(x_1086);
lean_dec(x_1105);
x_1107 = lean_unsigned_to_nat(0u);
x_1108 = l_Lean_Expr_getAppNumArgsAux(x_1090, x_1107);
x_1109 = lean_nat_dec_lt(x_1106, x_1108);
if (x_1109 == 0)
{
lean_dec(x_1108);
lean_dec(x_1106);
lean_dec(x_1090);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_1094, 0, x_1);
return x_1094;
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_free_object(x_1094);
lean_dec(x_1);
x_1110 = lean_nat_sub(x_1108, x_1106);
lean_dec(x_1106);
lean_dec(x_1108);
x_1111 = lean_unsigned_to_nat(1u);
x_1112 = lean_nat_sub(x_1110, x_1111);
lean_dec(x_1110);
x_1113 = l_Lean_Expr_getRevArg_x21(x_1090, x_1112);
lean_dec(x_1090);
x_1 = x_1113;
x_6 = x_1102;
goto _start;
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; 
x_1115 = lean_ctor_get(x_1094, 1);
lean_inc(x_1115);
lean_dec(x_1094);
x_1116 = lean_ctor_get(x_1100, 0);
lean_inc(x_1116);
lean_dec(x_1100);
x_1117 = lean_ctor_get(x_1116, 3);
lean_inc(x_1117);
lean_dec(x_1116);
x_1118 = lean_nat_add(x_1117, x_1086);
lean_dec(x_1086);
lean_dec(x_1117);
x_1119 = lean_unsigned_to_nat(0u);
x_1120 = l_Lean_Expr_getAppNumArgsAux(x_1090, x_1119);
x_1121 = lean_nat_dec_lt(x_1118, x_1120);
if (x_1121 == 0)
{
lean_object* x_1122; 
lean_dec(x_1120);
lean_dec(x_1118);
lean_dec(x_1090);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1122, 0, x_1);
lean_ctor_set(x_1122, 1, x_1115);
return x_1122;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1);
x_1123 = lean_nat_sub(x_1120, x_1118);
lean_dec(x_1118);
lean_dec(x_1120);
x_1124 = lean_unsigned_to_nat(1u);
x_1125 = lean_nat_sub(x_1123, x_1124);
lean_dec(x_1123);
x_1126 = l_Lean_Expr_getRevArg_x21(x_1090, x_1125);
lean_dec(x_1090);
x_1 = x_1126;
x_6 = x_1115;
goto _start;
}
}
}
else
{
uint8_t x_1128; 
lean_dec(x_1100);
lean_dec(x_1090);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1128 = !lean_is_exclusive(x_1094);
if (x_1128 == 0)
{
lean_object* x_1129; 
x_1129 = lean_ctor_get(x_1094, 0);
lean_dec(x_1129);
lean_ctor_set(x_1094, 0, x_1);
return x_1094;
}
else
{
lean_object* x_1130; lean_object* x_1131; 
x_1130 = lean_ctor_get(x_1094, 1);
lean_inc(x_1130);
lean_dec(x_1094);
x_1131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1131, 0, x_1);
lean_ctor_set(x_1131, 1, x_1130);
return x_1131;
}
}
}
}
else
{
uint8_t x_1132; 
lean_dec(x_1090);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1132 = !lean_is_exclusive(x_1094);
if (x_1132 == 0)
{
return x_1094;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1094, 0);
x_1134 = lean_ctor_get(x_1094, 1);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1094);
x_1135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set(x_1135, 1, x_1134);
return x_1135;
}
}
}
else
{
lean_dec(x_1092);
lean_dec(x_1090);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_1088, 0, x_1);
return x_1088;
}
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1136 = lean_ctor_get(x_1088, 0);
x_1137 = lean_ctor_get(x_1088, 1);
lean_inc(x_1137);
lean_inc(x_1136);
lean_dec(x_1088);
x_1138 = l_Lean_Expr_getAppFn(x_1136);
if (lean_obj_tag(x_1138) == 4)
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_ctor_get(x_1138, 0);
lean_inc(x_1139);
lean_dec(x_1138);
x_1140 = l_Lean_Meta_getConst_x3f(x_1139, x_2, x_3, x_4, x_5, x_1137);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_1136);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1143 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1143 = lean_box(0);
}
if (lean_is_scalar(x_1143)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1143;
}
lean_ctor_set(x_1144, 0, x_1);
lean_ctor_set(x_1144, 1, x_1142);
return x_1144;
}
else
{
lean_object* x_1145; 
x_1145 = lean_ctor_get(x_1141, 0);
lean_inc(x_1145);
lean_dec(x_1141);
if (lean_obj_tag(x_1145) == 6)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; 
x_1146 = lean_ctor_get(x_1140, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1147 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1147 = lean_box(0);
}
x_1148 = lean_ctor_get(x_1145, 0);
lean_inc(x_1148);
lean_dec(x_1145);
x_1149 = lean_ctor_get(x_1148, 3);
lean_inc(x_1149);
lean_dec(x_1148);
x_1150 = lean_nat_add(x_1149, x_1086);
lean_dec(x_1086);
lean_dec(x_1149);
x_1151 = lean_unsigned_to_nat(0u);
x_1152 = l_Lean_Expr_getAppNumArgsAux(x_1136, x_1151);
x_1153 = lean_nat_dec_lt(x_1150, x_1152);
if (x_1153 == 0)
{
lean_object* x_1154; 
lean_dec(x_1152);
lean_dec(x_1150);
lean_dec(x_1136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_1147)) {
 x_1154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1154 = x_1147;
}
lean_ctor_set(x_1154, 0, x_1);
lean_ctor_set(x_1154, 1, x_1146);
return x_1154;
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1147);
lean_dec(x_1);
x_1155 = lean_nat_sub(x_1152, x_1150);
lean_dec(x_1150);
lean_dec(x_1152);
x_1156 = lean_unsigned_to_nat(1u);
x_1157 = lean_nat_sub(x_1155, x_1156);
lean_dec(x_1155);
x_1158 = l_Lean_Expr_getRevArg_x21(x_1136, x_1157);
lean_dec(x_1136);
x_1 = x_1158;
x_6 = x_1146;
goto _start;
}
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1145);
lean_dec(x_1136);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1160 = lean_ctor_get(x_1140, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1161 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1161 = lean_box(0);
}
if (lean_is_scalar(x_1161)) {
 x_1162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1162 = x_1161;
}
lean_ctor_set(x_1162, 0, x_1);
lean_ctor_set(x_1162, 1, x_1160);
return x_1162;
}
}
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1136);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1163 = lean_ctor_get(x_1140, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1140, 1);
lean_inc(x_1164);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1165 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1165 = lean_box(0);
}
if (lean_is_scalar(x_1165)) {
 x_1166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1166 = x_1165;
}
lean_ctor_set(x_1166, 0, x_1163);
lean_ctor_set(x_1166, 1, x_1164);
return x_1166;
}
}
else
{
lean_object* x_1167; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_1);
lean_ctor_set(x_1167, 1, x_1137);
return x_1167;
}
}
}
else
{
uint8_t x_1168; 
lean_dec(x_1086);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1168 = !lean_is_exclusive(x_1088);
if (x_1168 == 0)
{
return x_1088;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1169 = lean_ctor_get(x_1088, 0);
x_1170 = lean_ctor_get(x_1088, 1);
lean_inc(x_1170);
lean_inc(x_1169);
lean_dec(x_1088);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1169);
lean_ctor_set(x_1171, 1, x_1170);
return x_1171;
}
}
}
default: 
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
lean_dec(x_1);
x_1172 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_1173 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
x_1174 = lean_panic_fn(x_1172, x_1173);
x_1175 = lean_apply_5(x_1174, x_2, x_3, x_4, x_5, x_917);
return x_1175;
}
}
}
}
case 12:
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_1);
x_1192 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_1193 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_1194 = lean_panic_fn(x_1192, x_1193);
x_1195 = lean_apply_5(x_1194, x_2, x_3, x_4, x_5, x_6);
return x_1195;
}
default: 
{
lean_object* x_1196; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1196, 0, x_1);
lean_ctor_set(x_1196, 1, x_6);
return x_1196;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_whnfCore___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_whnfCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_synthPending(x_17, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_1 = x_8;
x_6 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
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
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck(x_18, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1(x_17, x_8, x_2, x_3, x_4, x_5, x_18);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_30);
x_48 = l_Lean_ConstantInfo_name(x_41);
x_49 = l_Lean_Meta_smartUnfoldingSuffix;
x_50 = lean_name_mk_string(x_48, x_49);
x_51 = l_Lean_Meta_getConstNoEx_x3f(x_50, x_2, x_3, x_4, x_5, x_39);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_51);
x_58 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_59);
x_61 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_41, x_29, x_60, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_60);
lean_dec(x_29);
lean_dec(x_41);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_dec(x_51);
x_63 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_67);
x_69 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_41, x_29, x_68, x_2, x_3, x_4, x_5, x_62);
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
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
lean_dec(x_52);
if (lean_obj_tag(x_70) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_41);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_dec(x_51);
x_72 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_73 = lean_mk_empty_array_with_capacity(x_72);
lean_dec(x_72);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_73);
x_75 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(x_70, x_29, x_74, x_2, x_3, x_4, x_5, x_71);
lean_dec(x_74);
lean_dec(x_29);
lean_dec(x_70);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_70);
x_76 = !lean_is_exclusive(x_51);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_51, 1);
x_78 = lean_ctor_get(x_51, 0);
lean_dec(x_78);
x_79 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
lean_ctor_set(x_51, 0, x_80);
return x_51;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_51);
x_81 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_82 = lean_mk_empty_array_with_capacity(x_81);
lean_dec(x_81);
x_83 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_82);
x_84 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_41, x_29, x_83, x_2, x_3, x_4, x_5, x_77);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_83);
lean_dec(x_29);
lean_dec(x_41);
return x_84;
}
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_51, 1);
lean_inc(x_85);
lean_dec(x_51);
x_86 = l_Lean_ConstantInfo_hasValue(x_41);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = l_Lean_Expr_getAppNumArgsAux(x_1, x_43);
x_90 = lean_mk_empty_array_with_capacity(x_89);
lean_dec(x_89);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_90);
x_92 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_41, x_29, x_91, x_2, x_3, x_4, x_5, x_85);
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
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_30, 1);
lean_inc(x_93);
lean_dec(x_30);
x_94 = lean_ctor_get(x_31, 0);
lean_inc(x_94);
lean_dec(x_31);
x_95 = l_Lean_ConstantInfo_lparams(x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_List_lengthAux___rarg(x_95, x_96);
lean_dec(x_95);
x_98 = l_List_lengthAux___rarg(x_29, x_96);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_93);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = l_Lean_ConstantInfo_name(x_94);
x_103 = l_Lean_Meta_smartUnfoldingSuffix;
x_104 = lean_name_mk_string(x_102, x_103);
x_105 = l_Lean_Meta_getConstNoEx_x3f(x_104, x_2, x_3, x_4, x_5, x_93);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
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
x_109 = l_Lean_ConstantInfo_hasValue(x_94);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_108);
x_112 = l_Lean_Expr_getAppNumArgsAux(x_1, x_96);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
x_114 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_113);
x_115 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_94, x_29, x_114, x_2, x_3, x_4, x_5, x_107);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_114);
lean_dec(x_29);
lean_dec(x_94);
return x_115;
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec(x_106);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_94);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_dec(x_105);
x_118 = l_Lean_Expr_getAppNumArgsAux(x_1, x_96);
x_119 = lean_mk_empty_array_with_capacity(x_118);
lean_dec(x_118);
x_120 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_119);
x_121 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(x_116, x_29, x_120, x_2, x_3, x_4, x_5, x_117);
lean_dec(x_120);
lean_dec(x_29);
lean_dec(x_116);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_116);
x_122 = lean_ctor_get(x_105, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_123 = x_105;
} else {
 lean_dec_ref(x_105);
 x_123 = lean_box(0);
}
x_124 = l_Lean_ConstantInfo_hasValue(x_94);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_94);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_123);
x_127 = l_Lean_Expr_getAppNumArgsAux(x_1, x_96);
x_128 = lean_mk_empty_array_with_capacity(x_127);
lean_dec(x_127);
x_129 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_128);
x_130 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_94, x_29, x_129, x_2, x_3, x_4, x_5, x_122);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_129);
lean_dec(x_29);
lean_dec(x_94);
return x_130;
}
}
}
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_30);
if (x_131 == 0)
{
return x_30;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_30, 0);
x_133 = lean_ctor_get(x_30, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_30);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_6);
return x_136;
}
}
default: 
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_6);
return x_138;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDefinition_x3f___rarg), 2, 0);
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
x_10 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_995____spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__2;
x_8 = l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
x_2 = l_Lean_Lean_Exception___instance__1___closed__1;
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
x_2 = l_Lean_Lean_Exception___instance__1___closed__1;
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
x_1 = l_Lean_mkAppStx___closed__2;
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
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__6;
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
x_24 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_31 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_45 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_64 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_21 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_33 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_20 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_34 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_1 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1;
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
x_2 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_1);
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
x_1 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_2 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_25 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_15);
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
x_104 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_96);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_160 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_164 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_153);
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
x_232 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_224);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_293 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_291);
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
x_306 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_317 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_292);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_381 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_292);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
lean_inc(x_374);
x_387 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_374);
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
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_25 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_15);
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
x_118 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_122 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_111);
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
x_200 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_3, x_4, x_5, x_6, x_7, x_198);
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
x_212 = l_Lean_Meta_toCtorIfLit___closed__4;
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
x_227 = l_Lean_Meta_toCtorIfLit___closed__4;
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
lean_object* x_1; 
x_1 = lean_mk_string("beq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
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
x_1 = l_Lean_Literal_type___closed__2;
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
x_12 = l_Lean_Meta_toCtorIfLit___closed__2;
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
x_42 = l_Nat_Init_Data_Nat_Div___instance__2___closed__1;
x_43 = l_Lean_Meta_reduceBinNatOp(x_42, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_21);
x_44 = l_Nat_Init_Data_Nat_Div___instance__1___closed__1;
x_45 = l_Lean_Meta_reduceBinNatOp(x_44, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = l_Nat_Init_Data_Nat_Basic___instance__5___closed__1;
x_47 = l_Lean_Meta_reduceBinNatOp(x_46, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
x_48 = l_Nat_Init_Data_Nat_Basic___instance__4___closed__1;
x_49 = l_Lean_Meta_reduceBinNatOp(x_48, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_21);
x_50 = l_Init_Core___instance__2___closed__1;
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
x_12 = l_Lean_Meta_TransparencyMode_beq(x_10, x_11);
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
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
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
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__1;
x_3 = lean_unsigned_to_nat(412u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_4, x_7);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, 5);
lean_dec(x_11);
switch (x_12) {
case 0:
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_16, x_2);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_21, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_27, x_2);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_32, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_37 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_38 = lean_panic_fn(x_36, x_37);
x_39 = lean_apply_5(x_38, x_3, x_4, x_5, x_6, x_35);
return x_39;
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
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
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
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
x_3 = lean_unsigned_to_nat(422u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
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
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, 5);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_st_ref_take(x_5, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_3);
x_20 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_19, x_2, x_3);
lean_ctor_set(x_14, 4, x_20);
x_21 = lean_st_ref_set(x_5, x_13, x_15);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
x_28 = lean_ctor_get(x_14, 2);
x_29 = lean_ctor_get(x_14, 3);
x_30 = lean_ctor_get(x_14, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
lean_inc(x_3);
x_31 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_30, x_2, x_3);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_13, 1, x_32);
x_33 = lean_st_ref_set(x_5, x_13, x_15);
lean_dec(x_5);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 2);
x_39 = lean_ctor_get(x_13, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 4);
lean_inc(x_44);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_45 = x_14;
} else {
 lean_dec_ref(x_14);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_44, x_2, x_3);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 5, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_38);
lean_ctor_set(x_48, 3, x_39);
x_49 = lean_st_ref_set(x_5, x_48, x_15);
lean_dec(x_5);
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
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
case 1:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_53 = lean_st_ref_take(x_5, x_8);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_55, 3);
lean_inc(x_3);
x_61 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_60, x_2, x_3);
lean_ctor_set(x_55, 3, x_61);
x_62 = lean_st_ref_set(x_5, x_54, x_56);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_3);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
x_69 = lean_ctor_get(x_55, 2);
x_70 = lean_ctor_get(x_55, 4);
x_71 = lean_ctor_get(x_55, 3);
lean_inc(x_70);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
lean_inc(x_3);
x_72 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_71, x_2, x_3);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_54, 1, x_73);
x_74 = lean_st_ref_set(x_5, x_54, x_56);
lean_dec(x_5);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_3);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_78 = lean_ctor_get(x_54, 0);
x_79 = lean_ctor_get(x_54, 2);
x_80 = lean_ctor_get(x_54, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_54);
x_81 = lean_ctor_get(x_55, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_55, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_55, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_55, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_55, 3);
lean_inc(x_85);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 x_86 = x_55;
} else {
 lean_dec_ref(x_55);
 x_86 = lean_box(0);
}
lean_inc(x_3);
x_87 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_85, x_2, x_3);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_82);
lean_ctor_set(x_88, 2, x_83);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set(x_88, 4, x_84);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_79);
lean_ctor_set(x_89, 3, x_80);
x_90 = lean_st_ref_set(x_5, x_89, x_56);
lean_dec(x_5);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
default: 
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
x_94 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_95 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
x_96 = lean_panic_fn(x_94, x_95);
x_97 = lean_apply_5(x_96, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set(x_97, 0, x_3);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_3);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_97);
if (x_102 == 0)
{
return x_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
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
lean_object* l_Lean_Meta_whnfImp_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_whnfImp_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImp_match__5___rarg), 2, 0);
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
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
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
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(x_2, x_3, x_4, x_5, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, 6);
if (x_23 == 0)
{
if (x_20 == 0)
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_1 = x_19;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_st_ref_take(x_3, x_27);
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
x_33 = lean_box(0);
x_34 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_32, x_11, x_33);
lean_ctor_set(x_29, 2, x_34);
x_35 = lean_st_ref_set(x_3, x_29, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_1 = x_19;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
x_41 = lean_ctor_get(x_29, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_42 = lean_box(0);
x_43 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_11, x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_41);
x_45 = lean_st_ref_set(x_3, x_44, x_30);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_1 = x_19;
x_6 = x_46;
goto _start;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_21, 0);
lean_dec(x_49);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_1);
x_52 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_11);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_dec(x_21);
x_1 = x_19;
x_6 = x_53;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_st_ref_take(x_3, x_55);
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
x_61 = lean_box(0);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_60, x_11, x_61);
lean_ctor_set(x_57, 2, x_62);
x_63 = lean_st_ref_set(x_3, x_57, x_58);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_1 = x_19;
x_6 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
x_68 = lean_ctor_get(x_57, 2);
x_69 = lean_ctor_get(x_57, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_70 = lean_box(0);
x_71 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_68, x_11, x_70);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_69);
x_73 = lean_st_ref_set(x_3, x_72, x_58);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_1 = x_19;
x_6 = x_74;
goto _start;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_12);
if (x_76 == 0)
{
return x_12;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_80, x_2, x_3, x_4, x_5, x_6);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_1 = x_88;
x_6 = x_87;
goto _start;
}
}
case 4:
{
uint8_t x_90; lean_object* x_91; uint8_t x_161; 
x_161 = l_Lean_Expr_hasFVar(x_1);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasExprMVar(x_1);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_163, 5);
lean_dec(x_163);
x_165 = 2;
x_166 = l_Lean_Meta_TransparencyMode_beq(x_164, x_165);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = 1;
x_90 = x_167;
x_91 = x_6;
goto block_160;
}
else
{
uint8_t x_168; 
x_168 = 0;
x_90 = x_168;
x_91 = x_6;
goto block_160;
}
}
else
{
uint8_t x_169; 
x_169 = 0;
x_90 = x_169;
x_91 = x_6;
goto block_160;
}
}
else
{
uint8_t x_170; 
x_170 = 0;
x_90 = x_170;
x_91 = x_6;
goto block_160;
}
block_160:
{
lean_object* x_92; lean_object* x_93; 
if (x_90 == 0)
{
lean_object* x_135; 
x_135 = lean_box(0);
x_92 = x_135;
x_93 = x_91;
goto block_134;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_st_ref_get(x_3, x_91);
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_137, 5);
lean_dec(x_137);
switch (x_138) {
case 0:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_141, 4);
lean_inc(x_142);
lean_dec(x_141);
x_143 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_142, x_1);
x_92 = x_143;
x_93 = x_140;
goto block_134;
}
case 1:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
lean_dec(x_136);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_146, 3);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_147, x_1);
x_92 = x_148;
x_93 = x_145;
goto block_134;
}
default: 
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_dec(x_136);
x_150 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_151 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_152 = lean_panic_fn(x_150, x_151);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_153 = lean_apply_5(x_152, x_2, x_3, x_4, x_5, x_149);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_92 = x_154;
x_93 = x_155;
goto block_134;
}
else
{
uint8_t x_156; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_153);
if (x_156 == 0)
{
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
block_134:
{
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_94; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_94 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_95);
x_97 = l_Lean_Meta_reduceNat_x3f(x_95, x_2, x_3, x_4, x_5, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_95);
x_100 = l_Lean_Meta_reduceNative_x3f(x_95, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_95);
x_103 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_95, x_2, x_3, x_4, x_5, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_90, x_1, x_95, x_2, x_3, x_4, x_5, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_95);
lean_dec(x_1);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_1 = x_108;
x_6 = x_107;
goto _start;
}
}
else
{
uint8_t x_110; 
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_103);
if (x_110 == 0)
{
return x_103;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_103, 0);
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_103);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_95);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
x_115 = lean_ctor_get(x_101, 0);
lean_inc(x_115);
lean_dec(x_101);
x_116 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_90, x_1, x_115, x_2, x_3, x_4, x_5, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_100);
if (x_117 == 0)
{
return x_100;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_100, 0);
x_119 = lean_ctor_get(x_100, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_100);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_95);
x_121 = lean_ctor_get(x_97, 1);
lean_inc(x_121);
lean_dec(x_97);
x_122 = lean_ctor_get(x_98, 0);
lean_inc(x_122);
lean_dec(x_98);
x_123 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_90, x_1, x_122, x_2, x_3, x_4, x_5, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_97);
if (x_124 == 0)
{
return x_97;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_97, 0);
x_126 = lean_ctor_get(x_97, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_97);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_94);
if (x_128 == 0)
{
return x_94;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_94, 0);
x_130 = lean_ctor_get(x_94, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_94);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_92, 0);
lean_inc(x_132);
lean_dec(x_92);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_93);
return x_133;
}
}
}
}
case 5:
{
uint8_t x_171; lean_object* x_172; uint8_t x_242; 
x_242 = l_Lean_Expr_hasFVar(x_1);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = l_Lean_Expr_hasExprMVar(x_1);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_2, 0);
lean_inc(x_244);
x_245 = lean_ctor_get_uint8(x_244, 5);
lean_dec(x_244);
x_246 = 2;
x_247 = l_Lean_Meta_TransparencyMode_beq(x_245, x_246);
if (x_247 == 0)
{
uint8_t x_248; 
x_248 = 1;
x_171 = x_248;
x_172 = x_6;
goto block_241;
}
else
{
uint8_t x_249; 
x_249 = 0;
x_171 = x_249;
x_172 = x_6;
goto block_241;
}
}
else
{
uint8_t x_250; 
x_250 = 0;
x_171 = x_250;
x_172 = x_6;
goto block_241;
}
}
else
{
uint8_t x_251; 
x_251 = 0;
x_171 = x_251;
x_172 = x_6;
goto block_241;
}
block_241:
{
lean_object* x_173; lean_object* x_174; 
if (x_171 == 0)
{
lean_object* x_216; 
x_216 = lean_box(0);
x_173 = x_216;
x_174 = x_172;
goto block_215;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_st_ref_get(x_3, x_172);
x_218 = lean_ctor_get(x_2, 0);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_218, 5);
lean_dec(x_218);
switch (x_219) {
case 0:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_217, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_222, 4);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_223, x_1);
x_173 = x_224;
x_174 = x_221;
goto block_215;
}
case 1:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_217, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_217, 1);
lean_inc(x_226);
lean_dec(x_217);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_227, 3);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_228, x_1);
x_173 = x_229;
x_174 = x_226;
goto block_215;
}
default: 
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_dec(x_217);
x_231 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_232 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_233 = lean_panic_fn(x_231, x_232);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_234 = lean_apply_5(x_233, x_2, x_3, x_4, x_5, x_230);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_173 = x_235;
x_174 = x_236;
goto block_215;
}
else
{
uint8_t x_237; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_234);
if (x_237 == 0)
{
return x_234;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_234, 0);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_234);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
}
}
block_215:
{
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_175; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_175 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_176);
x_178 = l_Lean_Meta_reduceNat_x3f(x_176, x_2, x_3, x_4, x_5, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_176);
x_181 = l_Lean_Meta_reduceNative_x3f(x_176, x_2, x_3, x_4, x_5, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_176);
x_184 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_176, x_2, x_3, x_4, x_5, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_171, x_1, x_176, x_2, x_3, x_4, x_5, x_186);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_176);
lean_dec(x_1);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
lean_dec(x_185);
x_1 = x_189;
x_6 = x_188;
goto _start;
}
}
else
{
uint8_t x_191; 
lean_dec(x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_184);
if (x_191 == 0)
{
return x_184;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_184, 0);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_184);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_176);
x_195 = lean_ctor_get(x_181, 1);
lean_inc(x_195);
lean_dec(x_181);
x_196 = lean_ctor_get(x_182, 0);
lean_inc(x_196);
lean_dec(x_182);
x_197 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_171, x_1, x_196, x_2, x_3, x_4, x_5, x_195);
return x_197;
}
}
else
{
uint8_t x_198; 
lean_dec(x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_181);
if (x_198 == 0)
{
return x_181;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_181, 0);
x_200 = lean_ctor_get(x_181, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_181);
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
lean_dec(x_176);
x_202 = lean_ctor_get(x_178, 1);
lean_inc(x_202);
lean_dec(x_178);
x_203 = lean_ctor_get(x_179, 0);
lean_inc(x_203);
lean_dec(x_179);
x_204 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_171, x_1, x_203, x_2, x_3, x_4, x_5, x_202);
return x_204;
}
}
else
{
uint8_t x_205; 
lean_dec(x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_178);
if (x_205 == 0)
{
return x_178;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_178, 0);
x_207 = lean_ctor_get(x_178, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_178);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_175);
if (x_209 == 0)
{
return x_175;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_175, 0);
x_211 = lean_ctor_get(x_175, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_175);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_173, 0);
lean_inc(x_213);
lean_dec(x_173);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_174);
return x_214;
}
}
}
}
case 8:
{
uint8_t x_252; lean_object* x_253; uint8_t x_323; 
x_323 = l_Lean_Expr_hasFVar(x_1);
if (x_323 == 0)
{
uint8_t x_324; 
x_324 = l_Lean_Expr_hasExprMVar(x_1);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; uint8_t x_327; uint8_t x_328; 
x_325 = lean_ctor_get(x_2, 0);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_325, 5);
lean_dec(x_325);
x_327 = 2;
x_328 = l_Lean_Meta_TransparencyMode_beq(x_326, x_327);
if (x_328 == 0)
{
uint8_t x_329; 
x_329 = 1;
x_252 = x_329;
x_253 = x_6;
goto block_322;
}
else
{
uint8_t x_330; 
x_330 = 0;
x_252 = x_330;
x_253 = x_6;
goto block_322;
}
}
else
{
uint8_t x_331; 
x_331 = 0;
x_252 = x_331;
x_253 = x_6;
goto block_322;
}
}
else
{
uint8_t x_332; 
x_332 = 0;
x_252 = x_332;
x_253 = x_6;
goto block_322;
}
block_322:
{
lean_object* x_254; lean_object* x_255; 
if (x_252 == 0)
{
lean_object* x_297; 
x_297 = lean_box(0);
x_254 = x_297;
x_255 = x_253;
goto block_296;
}
else
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_st_ref_get(x_3, x_253);
x_299 = lean_ctor_get(x_2, 0);
lean_inc(x_299);
x_300 = lean_ctor_get_uint8(x_299, 5);
lean_dec(x_299);
switch (x_300) {
case 0:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = lean_ctor_get(x_298, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 1);
lean_inc(x_302);
lean_dec(x_298);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_303, 4);
lean_inc(x_304);
lean_dec(x_303);
x_305 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_304, x_1);
x_254 = x_305;
x_255 = x_302;
goto block_296;
}
case 1:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_298, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_298, 1);
lean_inc(x_307);
lean_dec(x_298);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_308, 3);
lean_inc(x_309);
lean_dec(x_308);
x_310 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_309, x_1);
x_254 = x_310;
x_255 = x_307;
goto block_296;
}
default: 
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_298, 1);
lean_inc(x_311);
lean_dec(x_298);
x_312 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_313 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_314 = lean_panic_fn(x_312, x_313);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_315 = lean_apply_5(x_314, x_2, x_3, x_4, x_5, x_311);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_254 = x_316;
x_255 = x_317;
goto block_296;
}
else
{
uint8_t x_318; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = !lean_is_exclusive(x_315);
if (x_318 == 0)
{
return x_315;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_315);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
}
block_296:
{
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_256; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_256 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_257);
x_259 = l_Lean_Meta_reduceNat_x3f(x_257, x_2, x_3, x_4, x_5, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_257);
x_262 = l_Lean_Meta_reduceNative_x3f(x_257, x_2, x_3, x_4, x_5, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_257);
x_265 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_257, x_2, x_3, x_4, x_5, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_252, x_1, x_257, x_2, x_3, x_4, x_5, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_257);
lean_dec(x_1);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
lean_dec(x_265);
x_270 = lean_ctor_get(x_266, 0);
lean_inc(x_270);
lean_dec(x_266);
x_1 = x_270;
x_6 = x_269;
goto _start;
}
}
else
{
uint8_t x_272; 
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_265);
if (x_272 == 0)
{
return x_265;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_265, 0);
x_274 = lean_ctor_get(x_265, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_265);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_257);
x_276 = lean_ctor_get(x_262, 1);
lean_inc(x_276);
lean_dec(x_262);
x_277 = lean_ctor_get(x_263, 0);
lean_inc(x_277);
lean_dec(x_263);
x_278 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_252, x_1, x_277, x_2, x_3, x_4, x_5, x_276);
return x_278;
}
}
else
{
uint8_t x_279; 
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_262);
if (x_279 == 0)
{
return x_262;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_262, 0);
x_281 = lean_ctor_get(x_262, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_262);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_257);
x_283 = lean_ctor_get(x_259, 1);
lean_inc(x_283);
lean_dec(x_259);
x_284 = lean_ctor_get(x_260, 0);
lean_inc(x_284);
lean_dec(x_260);
x_285 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_252, x_1, x_284, x_2, x_3, x_4, x_5, x_283);
return x_285;
}
}
else
{
uint8_t x_286; 
lean_dec(x_257);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_259);
if (x_286 == 0)
{
return x_259;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_259, 0);
x_288 = lean_ctor_get(x_259, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_259);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_256);
if (x_290 == 0)
{
return x_256;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_256, 0);
x_292 = lean_ctor_get(x_256, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_256);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_254, 0);
lean_inc(x_294);
lean_dec(x_254);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_255);
return x_295;
}
}
}
}
case 10:
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_1, 1);
lean_inc(x_333);
lean_dec(x_1);
x_1 = x_333;
goto _start;
}
case 11:
{
uint8_t x_335; lean_object* x_336; uint8_t x_406; 
x_406 = l_Lean_Expr_hasFVar(x_1);
if (x_406 == 0)
{
uint8_t x_407; 
x_407 = l_Lean_Expr_hasExprMVar(x_1);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; uint8_t x_410; uint8_t x_411; 
x_408 = lean_ctor_get(x_2, 0);
lean_inc(x_408);
x_409 = lean_ctor_get_uint8(x_408, 5);
lean_dec(x_408);
x_410 = 2;
x_411 = l_Lean_Meta_TransparencyMode_beq(x_409, x_410);
if (x_411 == 0)
{
uint8_t x_412; 
x_412 = 1;
x_335 = x_412;
x_336 = x_6;
goto block_405;
}
else
{
uint8_t x_413; 
x_413 = 0;
x_335 = x_413;
x_336 = x_6;
goto block_405;
}
}
else
{
uint8_t x_414; 
x_414 = 0;
x_335 = x_414;
x_336 = x_6;
goto block_405;
}
}
else
{
uint8_t x_415; 
x_415 = 0;
x_335 = x_415;
x_336 = x_6;
goto block_405;
}
block_405:
{
lean_object* x_337; lean_object* x_338; 
if (x_335 == 0)
{
lean_object* x_380; 
x_380 = lean_box(0);
x_337 = x_380;
x_338 = x_336;
goto block_379;
}
else
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_st_ref_get(x_3, x_336);
x_382 = lean_ctor_get(x_2, 0);
lean_inc(x_382);
x_383 = lean_ctor_get_uint8(x_382, 5);
lean_dec(x_382);
switch (x_383) {
case 0:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_384 = lean_ctor_get(x_381, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_381, 1);
lean_inc(x_385);
lean_dec(x_381);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_386, 4);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_387, x_1);
x_337 = x_388;
x_338 = x_385;
goto block_379;
}
case 1:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = lean_ctor_get(x_381, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_381, 1);
lean_inc(x_390);
lean_dec(x_381);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_ctor_get(x_391, 3);
lean_inc(x_392);
lean_dec(x_391);
x_393 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_392, x_1);
x_337 = x_393;
x_338 = x_390;
goto block_379;
}
default: 
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_381, 1);
lean_inc(x_394);
lean_dec(x_381);
x_395 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_396 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_397 = lean_panic_fn(x_395, x_396);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_398 = lean_apply_5(x_397, x_2, x_3, x_4, x_5, x_394);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_337 = x_399;
x_338 = x_400;
goto block_379;
}
else
{
uint8_t x_401; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_398);
if (x_401 == 0)
{
return x_398;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_398, 0);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_398);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
}
}
block_379:
{
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_339; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_339 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_338);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_340);
x_342 = l_Lean_Meta_reduceNat_x3f(x_340, x_2, x_3, x_4, x_5, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
lean_inc(x_340);
x_345 = l_Lean_Meta_reduceNative_x3f(x_340, x_2, x_3, x_4, x_5, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_340);
x_348 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_340, x_2, x_3, x_4, x_5, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_335, x_1, x_340, x_2, x_3, x_4, x_5, x_350);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_340);
lean_dec(x_1);
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
lean_dec(x_348);
x_353 = lean_ctor_get(x_349, 0);
lean_inc(x_353);
lean_dec(x_349);
x_1 = x_353;
x_6 = x_352;
goto _start;
}
}
else
{
uint8_t x_355; 
lean_dec(x_340);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_355 = !lean_is_exclusive(x_348);
if (x_355 == 0)
{
return x_348;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_348, 0);
x_357 = lean_ctor_get(x_348, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_348);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_340);
x_359 = lean_ctor_get(x_345, 1);
lean_inc(x_359);
lean_dec(x_345);
x_360 = lean_ctor_get(x_346, 0);
lean_inc(x_360);
lean_dec(x_346);
x_361 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_335, x_1, x_360, x_2, x_3, x_4, x_5, x_359);
return x_361;
}
}
else
{
uint8_t x_362; 
lean_dec(x_340);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_362 = !lean_is_exclusive(x_345);
if (x_362 == 0)
{
return x_345;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_345, 0);
x_364 = lean_ctor_get(x_345, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_345);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_340);
x_366 = lean_ctor_get(x_342, 1);
lean_inc(x_366);
lean_dec(x_342);
x_367 = lean_ctor_get(x_343, 0);
lean_inc(x_367);
lean_dec(x_343);
x_368 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_335, x_1, x_367, x_2, x_3, x_4, x_5, x_366);
return x_368;
}
}
else
{
uint8_t x_369; 
lean_dec(x_340);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_342);
if (x_369 == 0)
{
return x_342;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_342, 0);
x_371 = lean_ctor_get(x_342, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_342);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_373 = !lean_is_exclusive(x_339);
if (x_373 == 0)
{
return x_339;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_339, 0);
x_375 = lean_ctor_get(x_339, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_339);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = lean_ctor_get(x_337, 0);
lean_inc(x_377);
lean_dec(x_337);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_338);
return x_378;
}
}
}
}
case 12:
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_1);
x_416 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_417 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_418 = lean_panic_fn(x_416, x_417);
x_419 = lean_apply_5(x_418, x_2, x_3, x_4, x_5, x_6);
return x_419;
}
default: 
{
lean_object* x_420; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_1);
lean_ctor_set(x_420, 1, x_6);
return x_420;
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
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whnfHeadPredImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfHeadPredImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_19 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_9, x_3, x_4, x_5, x_6, x_18);
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
x_27 = l_Lean_Meta_whnfHeadPredImp(x_26, x_1, x_3, x_4, x_5, x_6, x_25);
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
lean_object* l_Lean_Meta_whnfHeadPredImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredImp___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_whnfHeadPred___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_whnfHeadPred(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPred___rarg), 3, 0);
return x_2;
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
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
x_13 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
lean_dec(x_14);
x_22 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(x_3, x_4, x_5, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, 6);
if (x_24 == 0)
{
if (x_21 == 0)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_12);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_2 = x_20;
x_7 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_st_ref_take(x_4, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = lean_box(0);
x_35 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_33, x_12, x_34);
lean_ctor_set(x_30, 2, x_35);
x_36 = lean_st_ref_set(x_4, x_30, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_2 = x_20;
x_7 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
x_41 = lean_ctor_get(x_30, 2);
x_42 = lean_ctor_get(x_30, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_43 = lean_box(0);
x_44 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_41, x_12, x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_42);
x_46 = lean_st_ref_set(x_4, x_45, x_31);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_2 = x_20;
x_7 = x_47;
goto _start;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_22, 0);
lean_dec(x_50);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_dec(x_22);
x_2 = x_20;
x_7 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_st_ref_take(x_4, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_58, 2);
x_62 = lean_box(0);
x_63 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_61, x_12, x_62);
lean_ctor_set(x_58, 2, x_63);
x_64 = lean_st_ref_set(x_4, x_58, x_59);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_2 = x_20;
x_7 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
x_69 = lean_ctor_get(x_58, 2);
x_70 = lean_ctor_get(x_58, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_71 = lean_box(0);
x_72 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_69, x_12, x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_70);
x_74 = lean_st_ref_set(x_4, x_73, x_59);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_2 = x_20;
x_7 = x_75;
goto _start;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 2:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_81, x_3, x_4, x_5, x_6, x_7);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_2);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_2 = x_89;
x_7 = x_88;
goto _start;
}
}
case 4:
{
lean_object* x_91; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = l_Lean_Expr_isAppOf(x_93, x_1);
if (x_95 == 0)
{
lean_object* x_96; 
lean_free_object(x_91);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_93);
x_96 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_93, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
lean_ctor_set(x_96, 0, x_93);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
x_2 = x_103;
x_7 = x_102;
goto _start;
}
}
else
{
uint8_t x_105; 
lean_dec(x_93);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_91;
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_91, 0);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_91);
x_111 = l_Lean_Expr_isAppOf(x_109, x_1);
if (x_111 == 0)
{
lean_object* x_112; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_109);
x_112 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_109, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
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
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_109);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
lean_dec(x_113);
x_2 = x_118;
x_7 = x_117;
goto _start;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_112, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_122 = x_112;
} else {
 lean_dec_ref(x_112);
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
lean_object* x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_110);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_91);
if (x_125 == 0)
{
return x_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_91, 0);
x_127 = lean_ctor_get(x_91, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_91);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 5:
{
lean_object* x_129; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
x_133 = l_Lean_Expr_isAppOf(x_131, x_1);
if (x_133 == 0)
{
lean_object* x_134; 
lean_free_object(x_129);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_131);
x_134 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_131, x_3, x_4, x_5, x_6, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_131);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_131);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
lean_dec(x_135);
x_2 = x_141;
x_7 = x_140;
goto _start;
}
}
else
{
uint8_t x_143; 
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_134);
if (x_143 == 0)
{
return x_134;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_134, 0);
x_145 = lean_ctor_get(x_134, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_134);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_129;
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_129, 0);
x_148 = lean_ctor_get(x_129, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_129);
x_149 = l_Lean_Expr_isAppOf(x_147, x_1);
if (x_149 == 0)
{
lean_object* x_150; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_147);
x_150 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_147, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_147);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
x_2 = x_156;
x_7 = x_155;
goto _start;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_147);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
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
else
{
lean_object* x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_148);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_129);
if (x_163 == 0)
{
return x_129;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_129, 0);
x_165 = lean_ctor_get(x_129, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_129);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
case 8:
{
lean_object* x_167; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_167 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
x_171 = l_Lean_Expr_isAppOf(x_169, x_1);
if (x_171 == 0)
{
lean_object* x_172; 
lean_free_object(x_167);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_169);
x_172 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_169, x_3, x_4, x_5, x_6, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
lean_ctor_set(x_172, 0, x_169);
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_169);
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
lean_dec(x_173);
x_2 = x_179;
x_7 = x_178;
goto _start;
}
}
else
{
uint8_t x_181; 
lean_dec(x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = !lean_is_exclusive(x_172);
if (x_181 == 0)
{
return x_172;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_172, 0);
x_183 = lean_ctor_get(x_172, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_172);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_167;
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_167, 0);
x_186 = lean_ctor_get(x_167, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_167);
x_187 = l_Lean_Expr_isAppOf(x_185, x_1);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_185);
x_188 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_185, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_185);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_185);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
lean_dec(x_189);
x_2 = x_194;
x_7 = x_193;
goto _start;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_ctor_get(x_188, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_188, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_198 = x_188;
} else {
 lean_dec_ref(x_188);
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
else
{
lean_object* x_200; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_185);
lean_ctor_set(x_200, 1, x_186);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_167);
if (x_201 == 0)
{
return x_167;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_167, 0);
x_203 = lean_ctor_get(x_167, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_167);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 10:
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
lean_dec(x_2);
x_2 = x_205;
goto _start;
}
case 11:
{
lean_object* x_207; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_207 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
x_211 = l_Lean_Expr_isAppOf(x_209, x_1);
if (x_211 == 0)
{
lean_object* x_212; 
lean_free_object(x_207);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_209);
x_212 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_209, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_212, 0);
lean_dec(x_215);
lean_ctor_set(x_212, 0, x_209);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_209);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_dec(x_212);
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
lean_dec(x_213);
x_2 = x_219;
x_7 = x_218;
goto _start;
}
}
else
{
uint8_t x_221; 
lean_dec(x_209);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_212);
if (x_221 == 0)
{
return x_212;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_212, 0);
x_223 = lean_ctor_get(x_212, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_212);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_207;
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = lean_ctor_get(x_207, 0);
x_226 = lean_ctor_get(x_207, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_207);
x_227 = l_Lean_Expr_isAppOf(x_225, x_1);
if (x_227 == 0)
{
lean_object* x_228; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_225);
x_228 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_225, x_3, x_4, x_5, x_6, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_225);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
lean_dec(x_229);
x_2 = x_234;
x_7 = x_233;
goto _start;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_236 = lean_ctor_get(x_228, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_228, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_238 = x_228;
} else {
 lean_dec_ref(x_228);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_225);
lean_ctor_set(x_240, 1, x_226);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_207);
if (x_241 == 0)
{
return x_207;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_207, 0);
x_243 = lean_ctor_get(x_207, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_207);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
case 12:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_2);
x_245 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_246 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_247 = lean_panic_fn(x_245, x_246);
x_248 = lean_apply_5(x_247, x_3, x_4, x_5, x_6, x_7);
return x_248;
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
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_1);
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
x_16 = l_Lean_Expr_isAppOf(x_14, x_1);
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
lean_object* l_Lean_Meta_whnfUntil___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_whnfUntil(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whnfUntil___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4523_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_ToExpr(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
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
l_Lean_Meta_smartUnfoldingSuffix___closed__1 = _init_l_Lean_Meta_smartUnfoldingSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix___closed__1);
l_Lean_Meta_smartUnfoldingSuffix = _init_l_Lean_Meta_smartUnfoldingSuffix();
lean_mark_persistent(l_Lean_Meta_smartUnfoldingSuffix);
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
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4);
l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5);
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
l_Lean_Meta_reduceNat_x3f___closed__17 = _init_l_Lean_Meta_reduceNat_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_reduceNat_x3f___closed__17);
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4523_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
