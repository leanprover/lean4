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
extern lean_object* l_Lean_Expr_Lean_Expr___instance__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__3(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_916____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___boxed(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(lean_object*, lean_object*);
extern lean_object* l_Lean_listToExpr___rarg___closed__1;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Meta_unfoldDefinition_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isIdRhsApp___closed__2;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__5;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_HasMod___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_extractIdRhs(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__7;
lean_object* l_Lean_Meta_whnfImp_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_HasMul___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Substring_HasQuote___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__10;
uint8_t l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isRecStuck_x3f___at___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__1(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3(lean_object*);
lean_object* l_Lean_List_toExprAux___at_Lean_Meta_toCtorIfLit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec(lean_object*);
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*);
lean_object* l_Lean_Meta_whnfImp_match__3(lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__2(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreUnstuck_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__6;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Meta_getConfig___rarg(lean_object*);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_withNatValue_match__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
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
extern lean_object* l_Nat_HasAdd___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isQuotRecStuck_x3f_match__1(lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3(lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
lean_object* l_Lean_ofExcept___at_Lean_Meta_reduceBoolNativeUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaDefinition(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
lean_object* l_Lean_Meta_reduceNative_x3f_match__1(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__17;
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConstCheck___at_Lean_Meta_reduceBoolNativeUnsafe___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4520_(lean_object*);
extern lean_object* l_Nat_HasDiv___closed__1;
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
extern lean_object* l_Lean_Prod_hasQuote___rarg___closed__3;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__3(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_matchConstAux_match__1(lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
extern lean_object* l_Nat_HasSub___closed__1;
lean_object* l_Lean_Meta_reduceNatNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__1;
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_listToExpr___rarg___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getStuckMVarImp_x3f_match__2(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__8;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor_match__1(lean_object*);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec_match__2(lean_object*);
extern lean_object* l_Lean_Expr_isCharLit___closed__2;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_getFirstCtor_match__1(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__9;
lean_object* l_Lean_Meta_whnfUntil(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
lean_object* l_Lean_Meta_whnfHeadPred___rarg(lean_object*, lean_object*, lean_object*);
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
x_31 = l_Array_shrink___main___rarg(x_30, x_2);
x_32 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_31, x_31, x_24, x_23);
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
x_42 = l_Array_shrink___main___rarg(x_41, x_2);
x_43 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_42, x_42, x_35, x_34);
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
x_56 = l_Array_shrink___main___rarg(x_55, x_2);
x_57 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_56, x_56, x_49, x_48);
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
x_1 = l_Lean_Substring_HasQuote___closed__2;
x_2 = l_Lean_Prod_hasQuote___rarg___closed__3;
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
x_1 = l_Lean_listToExpr___rarg___closed__1;
x_2 = l_Lean_Meta_toCtorIfLit___closed__9;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_toCtorIfLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_listToExpr___rarg___closed__2;
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
x_7 = l_List_find_x3f___main___rarg(x_5, x_6);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_5);
return x_9;
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_79 = l_Lean_Expr_getAppFn(x_13);
x_80 = l_Lean_RecursorVal_getInduct(x_1);
x_81 = l_Lean_Expr_isConstOf(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_82);
return x_8;
}
else
{
uint8_t x_83; 
lean_free_object(x_8);
x_83 = l_Lean_Expr_hasExprMVar(x_13);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_16 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Expr_getAppNumArgsAux(x_13, x_85);
x_87 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_86);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_86, x_89);
lean_dec(x_86);
lean_inc(x_13);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_88, x_90);
x_92 = lean_ctor_get(x_1, 2);
lean_inc(x_92);
x_93 = lean_array_get_size(x_91);
x_94 = lean_nat_dec_le(x_93, x_93);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3(x_13, x_91, x_93, x_92);
lean_dec(x_93);
lean_dec(x_91);
x_16 = x_95;
goto block_78;
}
else
{
uint8_t x_96; 
x_96 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4(x_13, lean_box(0), x_91, x_93, x_92);
lean_dec(x_93);
lean_dec(x_91);
x_16 = x_96;
goto block_78;
}
}
}
block_78:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_13);
x_18 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_13, x_17, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_29 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_28, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_13, x_30, x_3, x_4, x_5, x_6, x_31);
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
lean_free_object(x_19);
lean_dec(x_28);
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
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_32, 0);
lean_dec(x_42);
lean_ctor_set(x_32, 0, x_19);
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_19);
lean_dec(x_28);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_free_object(x_19);
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_53);
x_54 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_53, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_13, x_55, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_53);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_53);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_70 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_ctor_get(x_54, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_74 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_15;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_14);
return x_77;
}
}
}
else
{
uint8_t x_97; 
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_12);
if (x_97 == 0)
{
return x_12;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_12, 0);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_12);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_8, 0);
x_102 = lean_ctor_get(x_8, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_103 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_101, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_143 = l_Lean_Expr_getAppFn(x_104);
x_144 = l_Lean_RecursorVal_getInduct(x_1);
x_145 = l_Lean_Expr_isConstOf(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_105);
return x_147;
}
else
{
uint8_t x_148; 
x_148 = l_Lean_Expr_hasExprMVar(x_104);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = 0;
x_107 = x_149;
goto block_142;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Lean_Expr_getAppNumArgsAux(x_104, x_150);
x_152 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_151);
x_153 = lean_mk_array(x_151, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_sub(x_151, x_154);
lean_dec(x_151);
lean_inc(x_104);
x_156 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_104, x_153, x_155);
x_157 = lean_ctor_get(x_1, 2);
lean_inc(x_157);
x_158 = lean_array_get_size(x_156);
x_159 = lean_nat_dec_le(x_158, x_158);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3(x_104, x_156, x_158, x_157);
lean_dec(x_158);
lean_dec(x_156);
x_107 = x_160;
goto block_142;
}
else
{
uint8_t x_161; 
x_161 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4(x_104, lean_box(0), x_156, x_158, x_157);
lean_dec(x_158);
lean_dec(x_156);
x_107 = x_161;
goto block_142;
}
}
}
block_142:
{
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_106);
x_108 = lean_ctor_get(x_1, 2);
lean_inc(x_108);
lean_dec(x_1);
lean_inc(x_104);
x_109 = l___private_Lean_Meta_WHNF_0__Lean_Meta_mkNullaryCtor(x_104, x_108, x_3, x_4, x_5, x_6, x_105);
lean_dec(x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_104);
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
x_118 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_116, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_104, x_119, x_3, x_4, x_5, x_6, x_120);
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
lean_dec(x_104);
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
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_106;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_105);
return x_141;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_ctor_get(x_103, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_103, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_164 = x_103;
} else {
 lean_dec_ref(x_103);
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
}
else
{
uint8_t x_166; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_8);
if (x_166 == 0)
{
return x_8;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_8, 0);
x_168 = lean_ctor_get(x_8, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_8);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__4(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1;
x_16 = l_Lean_Meta_toCtorIfLit(x_8);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_WHNF_0__Lean_Meta_getRecRuleFor(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_19 = lean_apply_6(x_2, x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_15, x_20, x_10, x_11, x_12, x_13, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_71; uint8_t x_72; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux(x_16, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_16, x_31, x_33);
x_35 = l_List_lengthAux___main___rarg(x_3, x_28);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_71 = l_List_lengthAux___main___rarg(x_37, x_28);
x_72 = lean_nat_dec_eq(x_35, x_71);
lean_dec(x_71);
lean_dec(x_35);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = 1;
x_38 = x_73;
goto block_70;
}
else
{
uint8_t x_74; 
x_74 = 0;
x_38 = x_74;
goto block_70;
}
block_70:
{
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_39 = lean_ctor_get(x_27, 2);
lean_inc(x_39);
x_40 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_37, x_3, x_39);
lean_dec(x_37);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_44 = lean_ctor_get(x_1, 5);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_46 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_45, x_4, x_28, x_40);
lean_dec(x_45);
x_47 = lean_array_get_size(x_34);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_48);
x_50 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_47, x_34, x_49, x_46);
lean_dec(x_34);
lean_dec(x_47);
x_51 = lean_nat_add(x_5, x_32);
x_52 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_6, x_4, x_51, x_50);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_53 = lean_apply_6(x_7, x_52, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_apply_6(x_15, x_54, x_10, x_11, x_12, x_13, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_1);
x_61 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_62 = lean_apply_6(x_2, x_61, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_apply_6(x_15, x_63, x_10, x_11, x_12, x_13, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
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
x_22 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_19, x_21, x_6, x_7, x_8, x_9, x_20);
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
x_29 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_23, x_28, x_6, x_7, x_8, x_9, x_27);
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
x_33 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(x_1, x_4, x_2, x_3, x_11, x_12, x_5, x_31, x_32, x_6, x_7, x_8, x_9, x_30);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_37 = l_Lean_Expr_Lean_Expr___instance__1;
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
x_90 = l_Lean_Expr_Lean_Expr___instance__1;
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
x_3 = lean_unsigned_to_nat(205u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__2;
x_3 = lean_unsigned_to_nat(227u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 4);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
lean_dec(x_16);
x_24 = l_Lean_Meta_getConfig___rarg(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_5(x_24, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
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
if (x_23 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_29 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_26, 6);
if (x_54 == 0)
{
x_29 = x_23;
goto block_52;
}
else
{
uint8_t x_55; 
x_55 = 0;
x_29 = x_55;
goto block_52;
}
}
block_52:
{
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_28);
lean_dec(x_1);
x_30 = lean_ctor_get_uint8(x_26, 7);
lean_dec(x_26);
if (x_30 == 0)
{
lean_dec(x_12);
x_1 = x_22;
x_7 = x_27;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_take(x_4, x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_33, 2);
x_37 = lean_box(0);
x_38 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_36, x_12, x_37);
lean_ctor_set(x_33, 2, x_38);
x_39 = lean_st_ref_set(x_4, x_33, x_34);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_1 = x_22;
x_7 = x_40;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
x_44 = lean_ctor_get(x_33, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_45 = lean_box(0);
x_46 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_44, x_12, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_st_ref_set(x_4, x_47, x_34);
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
lean_object* x_51; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_28)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_28;
}
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_27);
return x_51;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 2:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_66 = l_Lean_Meta_getExprMVarAssignment_x3f___rarg(x_65, x_64);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_67 = lean_apply_5(x_66, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
lean_ctor_set(x_67, 0, x_1);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_1 = x_74;
x_7 = x_73;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_67);
if (x_76 == 0)
{
return x_67;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_67, 0);
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_67);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 4:
{
lean_object* x_80; 
x_80 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_80;
}
case 5:
{
lean_object* x_81; 
x_81 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_81;
}
case 8:
{
lean_object* x_82; 
x_82 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_82;
}
case 10:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_1 = x_83;
goto _start;
}
case 11:
{
lean_object* x_85; 
x_85 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_85;
}
case 12:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
lean_dec(x_1);
x_86 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_87 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_88 = lean_panic_fn(x_86, x_87);
x_89 = lean_apply_5(x_88, x_3, x_4, x_5, x_6, x_7);
return x_89;
}
default: 
{
lean_object* x_90; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_7);
return x_90;
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
x_13 = l_Lean_Expr_Lean_Expr___instance__1;
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
x_7 = l_List_lengthAux___main___rarg(x_5, x_6);
lean_dec(x_5);
x_8 = l_List_lengthAux___main___rarg(x_2, x_6);
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
x_8 = l_List_lengthAux___main___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthAux___main___rarg(x_2, x_7);
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
x_14 = l_List_lengthAux___main___rarg(x_12, x_13);
lean_dec(x_12);
x_15 = l_List_lengthAux___main___rarg(x_5, x_13);
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
x_1 = lean_mk_string("_private.Lean.Meta.WHNF.0.Lean.Meta.whnfCoreImp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(296u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
if (x_20 == 0)
{
uint8_t x_49; 
x_49 = 0;
x_25 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_22, 6);
if (x_50 == 0)
{
x_25 = x_20;
goto block_48;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_25 = x_51;
goto block_48;
}
}
block_48:
{
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_24);
lean_dec(x_1);
x_26 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_26 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_3, x_23);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_11, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_st_ref_set(x_3, x_43, x_30);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_1 = x_19;
x_6 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_24)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_24;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_23);
return x_47;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_56, x_2, x_3, x_4, x_5, x_6);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
lean_ctor_set(x_57, 0, x_1);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_1 = x_64;
x_6 = x_63;
goto _start;
}
}
case 4:
{
lean_object* x_66; uint8_t x_326; lean_object* x_327; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_333 = lean_st_ref_get(x_5, x_6);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_334, 3);
lean_inc(x_335);
lean_dec(x_334);
x_336 = lean_ctor_get_uint8(x_335, sizeof(void*)*1);
lean_dec(x_335);
if (x_336 == 0)
{
lean_object* x_337; uint8_t x_338; 
x_337 = lean_ctor_get(x_333, 1);
lean_inc(x_337);
lean_dec(x_333);
x_338 = 0;
x_326 = x_338;
x_327 = x_337;
goto block_332;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_339 = lean_ctor_get(x_333, 1);
lean_inc(x_339);
lean_dec(x_333);
x_340 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_341 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_340, x_2, x_3, x_4, x_5, x_339);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_unbox(x_342);
lean_dec(x_342);
x_326 = x_344;
x_327 = x_343;
goto block_332;
}
block_325:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
case 5:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = l_Lean_Expr_getAppFn(x_68);
lean_dec(x_68);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_69);
x_70 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_69, x_2, x_3, x_4, x_5, x_66);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = l_Lean_Expr_isLambda(x_72);
if (x_74 == 0)
{
if (lean_obj_tag(x_72) == 4)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_70);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_1);
lean_inc(x_72);
lean_inc(x_69);
x_77 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_77, 0, x_69);
lean_closure_set(x_77, 1, x_72);
lean_closure_set(x_77, 2, x_1);
x_78 = l_Lean_Meta_getConst_x3f(x_75, x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
x_82 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
lean_ctor_set(x_78, 0, x_83);
return x_78;
}
else
{
lean_dec(x_72);
lean_ctor_set(x_78, 0, x_1);
return x_78;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
lean_dec(x_79);
switch (lean_obj_tag(x_89)) {
case 1:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_77);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = l_Lean_ConstantInfo_name(x_89);
x_92 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_91, x_2, x_3, x_4, x_5, x_90);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
uint8_t x_95; 
lean_dec(x_89);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_92, 0);
lean_dec(x_96);
x_97 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
lean_ctor_set(x_92, 0, x_98);
return x_92;
}
else
{
lean_dec(x_72);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
x_100 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_72);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_92, 1);
lean_inc(x_104);
lean_dec(x_92);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Expr_getAppNumArgsAux(x_1, x_105);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_dec(x_106);
lean_inc(x_1);
x_108 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_107);
x_109 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_69, x_72, x_89, x_76, x_108, x_2, x_3, x_4, x_5, x_104);
lean_dec(x_108);
lean_dec(x_76);
lean_dec(x_89);
lean_dec(x_72);
lean_dec(x_69);
return x_109;
}
}
case 4:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_72);
lean_dec(x_69);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
lean_dec(x_78);
x_111 = lean_ctor_get(x_89, 0);
lean_inc(x_111);
lean_dec(x_89);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_Expr_getAppNumArgsAux(x_1, x_112);
x_114 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_113);
x_115 = lean_mk_array(x_113, x_114);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_sub(x_113, x_116);
lean_dec(x_113);
x_118 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_115, x_117);
x_119 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_120 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_111, x_76, x_118, x_77, x_119, x_2, x_3, x_4, x_5, x_110);
lean_dec(x_118);
lean_dec(x_76);
lean_dec(x_111);
return x_120;
}
case 7:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_72);
lean_dec(x_69);
x_121 = lean_ctor_get(x_78, 1);
lean_inc(x_121);
lean_dec(x_78);
x_122 = lean_ctor_get(x_89, 0);
lean_inc(x_122);
lean_dec(x_89);
x_123 = lean_unsigned_to_nat(0u);
x_124 = l_Lean_Expr_getAppNumArgsAux(x_1, x_123);
x_125 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_124);
x_126 = lean_mk_array(x_124, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_124, x_127);
lean_dec(x_124);
x_129 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_126, x_128);
x_130 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_131 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_122, x_76, x_129, x_77, x_130, x_2, x_3, x_4, x_5, x_121);
lean_dec(x_129);
lean_dec(x_76);
return x_131;
}
default: 
{
uint8_t x_132; 
lean_dec(x_89);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_78);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_78, 0);
lean_dec(x_133);
x_134 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
lean_ctor_set(x_78, 0, x_135);
return x_78;
}
else
{
lean_dec(x_72);
lean_ctor_set(x_78, 0, x_1);
return x_78;
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_78, 1);
lean_inc(x_136);
lean_dec(x_78);
x_137 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_72);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_78);
if (x_141 == 0)
{
return x_78;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_78, 0);
x_143 = lean_ctor_get(x_78, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_78);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_expr_eqv(x_69, x_72);
lean_dec(x_69);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = l_Lean_Expr_updateFn(x_1, x_72);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_146);
return x_70;
}
else
{
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_free_object(x_70);
lean_dec(x_69);
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Lean_Expr_getAppNumArgsAux(x_1, x_147);
x_149 = lean_mk_empty_array_with_capacity(x_148);
lean_dec(x_148);
x_150 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_149);
x_151 = l_Lean_Expr_betaRev(x_72, x_150);
lean_dec(x_150);
lean_dec(x_72);
x_1 = x_151;
x_6 = x_73;
goto _start;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_70, 0);
x_154 = lean_ctor_get(x_70, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_70);
x_155 = l_Lean_Expr_isLambda(x_153);
if (x_155 == 0)
{
if (lean_obj_tag(x_153) == 4)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_inc(x_1);
lean_inc(x_153);
lean_inc(x_69);
x_158 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_158, 0, x_69);
lean_closure_set(x_158, 1, x_153);
lean_closure_set(x_158, 2, x_1);
x_159 = l_Lean_Meta_getConst_x3f(x_156, x_2, x_3, x_4, x_5, x_154);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_expr_eqv(x_69, x_153);
lean_dec(x_69);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_updateFn(x_1, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_153);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_161);
return x_166;
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_160, 0);
lean_inc(x_167);
lean_dec(x_160);
switch (lean_obj_tag(x_167)) {
case 1:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_158);
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
lean_dec(x_159);
x_169 = l_Lean_ConstantInfo_name(x_167);
x_170 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_169, x_2, x_3, x_4, x_5, x_168);
lean_dec(x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_167);
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
x_175 = lean_expr_eqv(x_69, x_153);
lean_dec(x_69);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lean_Expr_updateFn(x_1, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_153);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_173);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_dec(x_170);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Lean_Expr_getAppNumArgsAux(x_1, x_180);
x_182 = lean_mk_empty_array_with_capacity(x_181);
lean_dec(x_181);
lean_inc(x_1);
x_183 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_182);
x_184 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_69, x_153, x_167, x_157, x_183, x_2, x_3, x_4, x_5, x_179);
lean_dec(x_183);
lean_dec(x_157);
lean_dec(x_167);
lean_dec(x_153);
lean_dec(x_69);
return x_184;
}
}
case 4:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_153);
lean_dec(x_69);
x_185 = lean_ctor_get(x_159, 1);
lean_inc(x_185);
lean_dec(x_159);
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
lean_dec(x_167);
x_187 = lean_unsigned_to_nat(0u);
x_188 = l_Lean_Expr_getAppNumArgsAux(x_1, x_187);
x_189 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_188);
x_190 = lean_mk_array(x_188, x_189);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_sub(x_188, x_191);
lean_dec(x_188);
x_193 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_190, x_192);
x_194 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_195 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_186, x_157, x_193, x_158, x_194, x_2, x_3, x_4, x_5, x_185);
lean_dec(x_193);
lean_dec(x_157);
lean_dec(x_186);
return x_195;
}
case 7:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_153);
lean_dec(x_69);
x_196 = lean_ctor_get(x_159, 1);
lean_inc(x_196);
lean_dec(x_159);
x_197 = lean_ctor_get(x_167, 0);
lean_inc(x_197);
lean_dec(x_167);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Lean_Expr_getAppNumArgsAux(x_1, x_198);
x_200 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_199);
x_201 = lean_mk_array(x_199, x_200);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_sub(x_199, x_202);
lean_dec(x_199);
x_204 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_201, x_203);
x_205 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_206 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_197, x_157, x_204, x_158, x_205, x_2, x_3, x_4, x_5, x_196);
lean_dec(x_204);
lean_dec(x_157);
return x_206;
}
default: 
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_ctor_get(x_159, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_208 = x_159;
} else {
 lean_dec_ref(x_159);
 x_208 = lean_box(0);
}
x_209 = lean_expr_eqv(x_69, x_153);
lean_dec(x_69);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = l_Lean_Expr_updateFn(x_1, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_207);
return x_211;
}
else
{
lean_object* x_212; 
lean_dec(x_153);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_207);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_153);
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_159, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_159, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_215 = x_159;
} else {
 lean_dec_ref(x_159);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_expr_eqv(x_69, x_153);
lean_dec(x_69);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = l_Lean_Expr_updateFn(x_1, x_153);
lean_dec(x_153);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_154);
return x_219;
}
else
{
lean_object* x_220; 
lean_dec(x_153);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_1);
lean_ctor_set(x_220, 1, x_154);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_69);
x_221 = lean_unsigned_to_nat(0u);
x_222 = l_Lean_Expr_getAppNumArgsAux(x_1, x_221);
x_223 = lean_mk_empty_array_with_capacity(x_222);
lean_dec(x_222);
x_224 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_223);
x_225 = l_Lean_Expr_betaRev(x_153, x_224);
lean_dec(x_224);
lean_dec(x_153);
x_1 = x_225;
x_6 = x_154;
goto _start;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_70);
if (x_227 == 0)
{
return x_70;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_70, 0);
x_229 = lean_ctor_get(x_70, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_70);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
case 8:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_1, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_1, 3);
lean_inc(x_232);
lean_dec(x_1);
x_233 = lean_expr_instantiate1(x_232, x_231);
lean_dec(x_231);
lean_dec(x_232);
x_1 = x_233;
x_6 = x_66;
goto _start;
}
case 11:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_1, 2);
lean_inc(x_236);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_237 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_236, x_2, x_3, x_4, x_5, x_66);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
x_241 = l_Lean_Expr_getAppFn(x_239);
if (lean_obj_tag(x_241) == 4)
{
lean_object* x_242; lean_object* x_243; 
lean_free_object(x_237);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec(x_241);
x_243 = l_Lean_Meta_getConst_x3f(x_242, x_2, x_3, x_4, x_5, x_240);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
lean_dec(x_239);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = !lean_is_exclusive(x_243);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_243, 0);
lean_dec(x_246);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_1);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
else
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
lean_dec(x_244);
if (lean_obj_tag(x_249) == 6)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_243);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_251 = lean_ctor_get(x_243, 1);
x_252 = lean_ctor_get(x_243, 0);
lean_dec(x_252);
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
lean_dec(x_249);
x_254 = lean_ctor_get(x_253, 3);
lean_inc(x_254);
lean_dec(x_253);
x_255 = lean_nat_add(x_254, x_235);
lean_dec(x_235);
lean_dec(x_254);
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Lean_Expr_getAppNumArgsAux(x_239, x_256);
x_258 = lean_nat_dec_lt(x_255, x_257);
if (x_258 == 0)
{
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_239);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_free_object(x_243);
lean_dec(x_1);
x_259 = lean_nat_sub(x_257, x_255);
lean_dec(x_255);
lean_dec(x_257);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_sub(x_259, x_260);
lean_dec(x_259);
x_262 = l_Lean_Expr_getRevArg_x21(x_239, x_261);
lean_dec(x_239);
x_1 = x_262;
x_6 = x_251;
goto _start;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_264 = lean_ctor_get(x_243, 1);
lean_inc(x_264);
lean_dec(x_243);
x_265 = lean_ctor_get(x_249, 0);
lean_inc(x_265);
lean_dec(x_249);
x_266 = lean_ctor_get(x_265, 3);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_nat_add(x_266, x_235);
lean_dec(x_235);
lean_dec(x_266);
x_268 = lean_unsigned_to_nat(0u);
x_269 = l_Lean_Expr_getAppNumArgsAux(x_239, x_268);
x_270 = lean_nat_dec_lt(x_267, x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_239);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_1);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_1);
x_272 = lean_nat_sub(x_269, x_267);
lean_dec(x_267);
lean_dec(x_269);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_sub(x_272, x_273);
lean_dec(x_272);
x_275 = l_Lean_Expr_getRevArg_x21(x_239, x_274);
lean_dec(x_239);
x_1 = x_275;
x_6 = x_264;
goto _start;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_249);
lean_dec(x_239);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = !lean_is_exclusive(x_243);
if (x_277 == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_243, 0);
lean_dec(x_278);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_243, 1);
lean_inc(x_279);
lean_dec(x_243);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_1);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_239);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_243);
if (x_281 == 0)
{
return x_243;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_243, 0);
x_283 = lean_ctor_get(x_243, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_243);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
lean_dec(x_241);
lean_dec(x_239);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_237, 0, x_1);
return x_237;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_237, 0);
x_286 = lean_ctor_get(x_237, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_237);
x_287 = l_Lean_Expr_getAppFn(x_285);
if (lean_obj_tag(x_287) == 4)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec(x_287);
x_289 = l_Lean_Meta_getConst_x3f(x_288, x_2, x_3, x_4, x_5, x_286);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_285);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_1);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
else
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_290, 0);
lean_inc(x_294);
lean_dec(x_290);
if (lean_obj_tag(x_294) == 6)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_295 = lean_ctor_get(x_289, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_296 = x_289;
} else {
 lean_dec_ref(x_289);
 x_296 = lean_box(0);
}
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_297, 3);
lean_inc(x_298);
lean_dec(x_297);
x_299 = lean_nat_add(x_298, x_235);
lean_dec(x_235);
lean_dec(x_298);
x_300 = lean_unsigned_to_nat(0u);
x_301 = l_Lean_Expr_getAppNumArgsAux(x_285, x_300);
x_302 = lean_nat_dec_lt(x_299, x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_285);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_296)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_296;
}
lean_ctor_set(x_303, 0, x_1);
lean_ctor_set(x_303, 1, x_295);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_296);
lean_dec(x_1);
x_304 = lean_nat_sub(x_301, x_299);
lean_dec(x_299);
lean_dec(x_301);
x_305 = lean_unsigned_to_nat(1u);
x_306 = lean_nat_sub(x_304, x_305);
lean_dec(x_304);
x_307 = l_Lean_Expr_getRevArg_x21(x_285, x_306);
lean_dec(x_285);
x_1 = x_307;
x_6 = x_295;
goto _start;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_294);
lean_dec(x_285);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_309 = lean_ctor_get(x_289, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_310 = x_289;
} else {
 lean_dec_ref(x_289);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_1);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_285);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_ctor_get(x_289, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_289, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_314 = x_289;
} else {
 lean_dec_ref(x_289);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
lean_object* x_316; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_1);
lean_ctor_set(x_316, 1, x_286);
return x_316;
}
}
}
else
{
uint8_t x_317; 
lean_dec(x_235);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = !lean_is_exclusive(x_237);
if (x_317 == 0)
{
return x_237;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_237, 0);
x_319 = lean_ctor_get(x_237, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_237);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
default: 
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_1);
x_321 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_322 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_323 = lean_panic_fn(x_321, x_322);
x_324 = lean_apply_5(x_323, x_2, x_3, x_4, x_5, x_66);
return x_324;
}
}
}
block_332:
{
if (x_326 == 0)
{
x_66 = x_327;
goto block_325;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_inc(x_1);
x_328 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_328, 0, x_1);
x_329 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_330 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_329, x_328, x_2, x_3, x_4, x_5, x_327);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_66 = x_331;
goto block_325;
}
}
}
case 5:
{
lean_object* x_345; uint8_t x_605; lean_object* x_606; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_612 = lean_st_ref_get(x_5, x_6);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_613, 3);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_ctor_get_uint8(x_614, sizeof(void*)*1);
lean_dec(x_614);
if (x_615 == 0)
{
lean_object* x_616; uint8_t x_617; 
x_616 = lean_ctor_get(x_612, 1);
lean_inc(x_616);
lean_dec(x_612);
x_617 = 0;
x_605 = x_617;
x_606 = x_616;
goto block_611;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; 
x_618 = lean_ctor_get(x_612, 1);
lean_inc(x_618);
lean_dec(x_612);
x_619 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_620 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_619, x_2, x_3, x_4, x_5, x_618);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_unbox(x_621);
lean_dec(x_621);
x_605 = x_623;
x_606 = x_622;
goto block_611;
}
block_604:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_346; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
case 5:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_1, 0);
lean_inc(x_347);
x_348 = l_Lean_Expr_getAppFn(x_347);
lean_dec(x_347);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_348);
x_349 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_348, x_2, x_3, x_4, x_5, x_345);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
x_353 = l_Lean_Expr_isLambda(x_351);
if (x_353 == 0)
{
if (lean_obj_tag(x_351) == 4)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_free_object(x_349);
x_354 = lean_ctor_get(x_351, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
lean_inc(x_1);
lean_inc(x_351);
lean_inc(x_348);
x_356 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_356, 0, x_348);
lean_closure_set(x_356, 1, x_351);
lean_closure_set(x_356, 2, x_1);
x_357 = l_Lean_Meta_getConst_x3f(x_354, x_2, x_3, x_4, x_5, x_352);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = !lean_is_exclusive(x_357);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_357, 0);
lean_dec(x_360);
x_361 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_361 == 0)
{
lean_object* x_362; 
x_362 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
lean_ctor_set(x_357, 0, x_362);
return x_357;
}
else
{
lean_dec(x_351);
lean_ctor_set(x_357, 0, x_1);
return x_357;
}
}
else
{
lean_object* x_363; uint8_t x_364; 
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_dec(x_357);
x_364 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
return x_366;
}
else
{
lean_object* x_367; 
lean_dec(x_351);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_1);
lean_ctor_set(x_367, 1, x_363);
return x_367;
}
}
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_358, 0);
lean_inc(x_368);
lean_dec(x_358);
switch (lean_obj_tag(x_368)) {
case 1:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_356);
x_369 = lean_ctor_get(x_357, 1);
lean_inc(x_369);
lean_dec(x_357);
x_370 = l_Lean_ConstantInfo_name(x_368);
x_371 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_370, x_2, x_3, x_4, x_5, x_369);
lean_dec(x_370);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_unbox(x_372);
lean_dec(x_372);
if (x_373 == 0)
{
uint8_t x_374; 
lean_dec(x_368);
lean_dec(x_355);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_374 = !lean_is_exclusive(x_371);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_371, 0);
lean_dec(x_375);
x_376 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_376 == 0)
{
lean_object* x_377; 
x_377 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
lean_ctor_set(x_371, 0, x_377);
return x_371;
}
else
{
lean_dec(x_351);
lean_ctor_set(x_371, 0, x_1);
return x_371;
}
}
else
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_371, 1);
lean_inc(x_378);
lean_dec(x_371);
x_379 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; 
x_380 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
return x_381;
}
else
{
lean_object* x_382; 
lean_dec(x_351);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_1);
lean_ctor_set(x_382, 1, x_378);
return x_382;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_ctor_get(x_371, 1);
lean_inc(x_383);
lean_dec(x_371);
x_384 = lean_unsigned_to_nat(0u);
x_385 = l_Lean_Expr_getAppNumArgsAux(x_1, x_384);
x_386 = lean_mk_empty_array_with_capacity(x_385);
lean_dec(x_385);
lean_inc(x_1);
x_387 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_386);
x_388 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_348, x_351, x_368, x_355, x_387, x_2, x_3, x_4, x_5, x_383);
lean_dec(x_387);
lean_dec(x_355);
lean_dec(x_368);
lean_dec(x_351);
lean_dec(x_348);
return x_388;
}
}
case 4:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_351);
lean_dec(x_348);
x_389 = lean_ctor_get(x_357, 1);
lean_inc(x_389);
lean_dec(x_357);
x_390 = lean_ctor_get(x_368, 0);
lean_inc(x_390);
lean_dec(x_368);
x_391 = lean_unsigned_to_nat(0u);
x_392 = l_Lean_Expr_getAppNumArgsAux(x_1, x_391);
x_393 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_392);
x_394 = lean_mk_array(x_392, x_393);
x_395 = lean_unsigned_to_nat(1u);
x_396 = lean_nat_sub(x_392, x_395);
lean_dec(x_392);
x_397 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_394, x_396);
x_398 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_399 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_390, x_355, x_397, x_356, x_398, x_2, x_3, x_4, x_5, x_389);
lean_dec(x_397);
lean_dec(x_355);
lean_dec(x_390);
return x_399;
}
case 7:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_351);
lean_dec(x_348);
x_400 = lean_ctor_get(x_357, 1);
lean_inc(x_400);
lean_dec(x_357);
x_401 = lean_ctor_get(x_368, 0);
lean_inc(x_401);
lean_dec(x_368);
x_402 = lean_unsigned_to_nat(0u);
x_403 = l_Lean_Expr_getAppNumArgsAux(x_1, x_402);
x_404 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_403);
x_405 = lean_mk_array(x_403, x_404);
x_406 = lean_unsigned_to_nat(1u);
x_407 = lean_nat_sub(x_403, x_406);
lean_dec(x_403);
x_408 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_405, x_407);
x_409 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_410 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_401, x_355, x_408, x_356, x_409, x_2, x_3, x_4, x_5, x_400);
lean_dec(x_408);
lean_dec(x_355);
return x_410;
}
default: 
{
uint8_t x_411; 
lean_dec(x_368);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_411 = !lean_is_exclusive(x_357);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; 
x_412 = lean_ctor_get(x_357, 0);
lean_dec(x_412);
x_413 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_413 == 0)
{
lean_object* x_414; 
x_414 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
lean_ctor_set(x_357, 0, x_414);
return x_357;
}
else
{
lean_dec(x_351);
lean_ctor_set(x_357, 0, x_1);
return x_357;
}
}
else
{
lean_object* x_415; uint8_t x_416; 
x_415 = lean_ctor_get(x_357, 1);
lean_inc(x_415);
lean_dec(x_357);
x_416 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_415);
return x_418;
}
else
{
lean_object* x_419; 
lean_dec(x_351);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_1);
lean_ctor_set(x_419, 1, x_415);
return x_419;
}
}
}
}
}
}
else
{
uint8_t x_420; 
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_351);
lean_dec(x_348);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_357);
if (x_420 == 0)
{
return x_357;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_357, 0);
x_422 = lean_ctor_get(x_357, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_357);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_424 = lean_expr_eqv(x_348, x_351);
lean_dec(x_348);
if (x_424 == 0)
{
lean_object* x_425; 
x_425 = l_Lean_Expr_updateFn(x_1, x_351);
lean_dec(x_351);
lean_ctor_set(x_349, 0, x_425);
return x_349;
}
else
{
lean_dec(x_351);
lean_ctor_set(x_349, 0, x_1);
return x_349;
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_free_object(x_349);
lean_dec(x_348);
x_426 = lean_unsigned_to_nat(0u);
x_427 = l_Lean_Expr_getAppNumArgsAux(x_1, x_426);
x_428 = lean_mk_empty_array_with_capacity(x_427);
lean_dec(x_427);
x_429 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_428);
x_430 = l_Lean_Expr_betaRev(x_351, x_429);
lean_dec(x_429);
lean_dec(x_351);
x_1 = x_430;
x_6 = x_352;
goto _start;
}
}
else
{
lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_432 = lean_ctor_get(x_349, 0);
x_433 = lean_ctor_get(x_349, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_349);
x_434 = l_Lean_Expr_isLambda(x_432);
if (x_434 == 0)
{
if (lean_obj_tag(x_432) == 4)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_435 = lean_ctor_get(x_432, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 1);
lean_inc(x_436);
lean_inc(x_1);
lean_inc(x_432);
lean_inc(x_348);
x_437 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_437, 0, x_348);
lean_closure_set(x_437, 1, x_432);
lean_closure_set(x_437, 2, x_1);
x_438 = l_Lean_Meta_getConst_x3f(x_435, x_2, x_3, x_4, x_5, x_433);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_441 = x_438;
} else {
 lean_dec_ref(x_438);
 x_441 = lean_box(0);
}
x_442 = lean_expr_eqv(x_348, x_432);
lean_dec(x_348);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = l_Lean_Expr_updateFn(x_1, x_432);
lean_dec(x_432);
if (lean_is_scalar(x_441)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_441;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_440);
return x_444;
}
else
{
lean_object* x_445; 
lean_dec(x_432);
if (lean_is_scalar(x_441)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_441;
}
lean_ctor_set(x_445, 0, x_1);
lean_ctor_set(x_445, 1, x_440);
return x_445;
}
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_439, 0);
lean_inc(x_446);
lean_dec(x_439);
switch (lean_obj_tag(x_446)) {
case 1:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_dec(x_437);
x_447 = lean_ctor_get(x_438, 1);
lean_inc(x_447);
lean_dec(x_438);
x_448 = l_Lean_ConstantInfo_name(x_446);
x_449 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_448, x_2, x_3, x_4, x_5, x_447);
lean_dec(x_448);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_unbox(x_450);
lean_dec(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_dec(x_446);
lean_dec(x_436);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_452 = lean_ctor_get(x_449, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_453 = x_449;
} else {
 lean_dec_ref(x_449);
 x_453 = lean_box(0);
}
x_454 = lean_expr_eqv(x_348, x_432);
lean_dec(x_348);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = l_Lean_Expr_updateFn(x_1, x_432);
lean_dec(x_432);
if (lean_is_scalar(x_453)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_453;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_452);
return x_456;
}
else
{
lean_object* x_457; 
lean_dec(x_432);
if (lean_is_scalar(x_453)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_453;
}
lean_ctor_set(x_457, 0, x_1);
lean_ctor_set(x_457, 1, x_452);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_458 = lean_ctor_get(x_449, 1);
lean_inc(x_458);
lean_dec(x_449);
x_459 = lean_unsigned_to_nat(0u);
x_460 = l_Lean_Expr_getAppNumArgsAux(x_1, x_459);
x_461 = lean_mk_empty_array_with_capacity(x_460);
lean_dec(x_460);
lean_inc(x_1);
x_462 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_461);
x_463 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_348, x_432, x_446, x_436, x_462, x_2, x_3, x_4, x_5, x_458);
lean_dec(x_462);
lean_dec(x_436);
lean_dec(x_446);
lean_dec(x_432);
lean_dec(x_348);
return x_463;
}
}
case 4:
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_432);
lean_dec(x_348);
x_464 = lean_ctor_get(x_438, 1);
lean_inc(x_464);
lean_dec(x_438);
x_465 = lean_ctor_get(x_446, 0);
lean_inc(x_465);
lean_dec(x_446);
x_466 = lean_unsigned_to_nat(0u);
x_467 = l_Lean_Expr_getAppNumArgsAux(x_1, x_466);
x_468 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_467);
x_469 = lean_mk_array(x_467, x_468);
x_470 = lean_unsigned_to_nat(1u);
x_471 = lean_nat_sub(x_467, x_470);
lean_dec(x_467);
x_472 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_469, x_471);
x_473 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_474 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_465, x_436, x_472, x_437, x_473, x_2, x_3, x_4, x_5, x_464);
lean_dec(x_472);
lean_dec(x_436);
lean_dec(x_465);
return x_474;
}
case 7:
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_432);
lean_dec(x_348);
x_475 = lean_ctor_get(x_438, 1);
lean_inc(x_475);
lean_dec(x_438);
x_476 = lean_ctor_get(x_446, 0);
lean_inc(x_476);
lean_dec(x_446);
x_477 = lean_unsigned_to_nat(0u);
x_478 = l_Lean_Expr_getAppNumArgsAux(x_1, x_477);
x_479 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_478);
x_480 = lean_mk_array(x_478, x_479);
x_481 = lean_unsigned_to_nat(1u);
x_482 = lean_nat_sub(x_478, x_481);
lean_dec(x_478);
x_483 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_480, x_482);
x_484 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_485 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_476, x_436, x_483, x_437, x_484, x_2, x_3, x_4, x_5, x_475);
lean_dec(x_483);
lean_dec(x_436);
return x_485;
}
default: 
{
lean_object* x_486; lean_object* x_487; uint8_t x_488; 
lean_dec(x_446);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_486 = lean_ctor_get(x_438, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_487 = x_438;
} else {
 lean_dec_ref(x_438);
 x_487 = lean_box(0);
}
x_488 = lean_expr_eqv(x_348, x_432);
lean_dec(x_348);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = l_Lean_Expr_updateFn(x_1, x_432);
lean_dec(x_432);
if (lean_is_scalar(x_487)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_487;
}
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_486);
return x_490;
}
else
{
lean_object* x_491; 
lean_dec(x_432);
if (lean_is_scalar(x_487)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_487;
}
lean_ctor_set(x_491, 0, x_1);
lean_ctor_set(x_491, 1, x_486);
return x_491;
}
}
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_348);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_492 = lean_ctor_get(x_438, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_438, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_494 = x_438;
} else {
 lean_dec_ref(x_438);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
else
{
uint8_t x_496; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_496 = lean_expr_eqv(x_348, x_432);
lean_dec(x_348);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; 
x_497 = l_Lean_Expr_updateFn(x_1, x_432);
lean_dec(x_432);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_433);
return x_498;
}
else
{
lean_object* x_499; 
lean_dec(x_432);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_1);
lean_ctor_set(x_499, 1, x_433);
return x_499;
}
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_348);
x_500 = lean_unsigned_to_nat(0u);
x_501 = l_Lean_Expr_getAppNumArgsAux(x_1, x_500);
x_502 = lean_mk_empty_array_with_capacity(x_501);
lean_dec(x_501);
x_503 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_502);
x_504 = l_Lean_Expr_betaRev(x_432, x_503);
lean_dec(x_503);
lean_dec(x_432);
x_1 = x_504;
x_6 = x_433;
goto _start;
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_348);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_349);
if (x_506 == 0)
{
return x_349;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_349, 0);
x_508 = lean_ctor_get(x_349, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_349);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
case 8:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_1, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_1, 3);
lean_inc(x_511);
lean_dec(x_1);
x_512 = lean_expr_instantiate1(x_511, x_510);
lean_dec(x_510);
lean_dec(x_511);
x_1 = x_512;
x_6 = x_345;
goto _start;
}
case 11:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_1, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_1, 2);
lean_inc(x_515);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_516 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_515, x_2, x_3, x_4, x_5, x_345);
if (lean_obj_tag(x_516) == 0)
{
uint8_t x_517; 
x_517 = !lean_is_exclusive(x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_516, 0);
x_519 = lean_ctor_get(x_516, 1);
x_520 = l_Lean_Expr_getAppFn(x_518);
if (lean_obj_tag(x_520) == 4)
{
lean_object* x_521; lean_object* x_522; 
lean_free_object(x_516);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
lean_dec(x_520);
x_522 = l_Lean_Meta_getConst_x3f(x_521, x_2, x_3, x_4, x_5, x_519);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
if (lean_obj_tag(x_523) == 0)
{
uint8_t x_524; 
lean_dec(x_518);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_524 = !lean_is_exclusive(x_522);
if (x_524 == 0)
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_522, 0);
lean_dec(x_525);
lean_ctor_set(x_522, 0, x_1);
return x_522;
}
else
{
lean_object* x_526; lean_object* x_527; 
x_526 = lean_ctor_get(x_522, 1);
lean_inc(x_526);
lean_dec(x_522);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_1);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
else
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_523, 0);
lean_inc(x_528);
lean_dec(x_523);
if (lean_obj_tag(x_528) == 6)
{
uint8_t x_529; 
x_529 = !lean_is_exclusive(x_522);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; 
x_530 = lean_ctor_get(x_522, 1);
x_531 = lean_ctor_get(x_522, 0);
lean_dec(x_531);
x_532 = lean_ctor_get(x_528, 0);
lean_inc(x_532);
lean_dec(x_528);
x_533 = lean_ctor_get(x_532, 3);
lean_inc(x_533);
lean_dec(x_532);
x_534 = lean_nat_add(x_533, x_514);
lean_dec(x_514);
lean_dec(x_533);
x_535 = lean_unsigned_to_nat(0u);
x_536 = l_Lean_Expr_getAppNumArgsAux(x_518, x_535);
x_537 = lean_nat_dec_lt(x_534, x_536);
if (x_537 == 0)
{
lean_dec(x_536);
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_522, 0, x_1);
return x_522;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_free_object(x_522);
lean_dec(x_1);
x_538 = lean_nat_sub(x_536, x_534);
lean_dec(x_534);
lean_dec(x_536);
x_539 = lean_unsigned_to_nat(1u);
x_540 = lean_nat_sub(x_538, x_539);
lean_dec(x_538);
x_541 = l_Lean_Expr_getRevArg_x21(x_518, x_540);
lean_dec(x_518);
x_1 = x_541;
x_6 = x_530;
goto _start;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_543 = lean_ctor_get(x_522, 1);
lean_inc(x_543);
lean_dec(x_522);
x_544 = lean_ctor_get(x_528, 0);
lean_inc(x_544);
lean_dec(x_528);
x_545 = lean_ctor_get(x_544, 3);
lean_inc(x_545);
lean_dec(x_544);
x_546 = lean_nat_add(x_545, x_514);
lean_dec(x_514);
lean_dec(x_545);
x_547 = lean_unsigned_to_nat(0u);
x_548 = l_Lean_Expr_getAppNumArgsAux(x_518, x_547);
x_549 = lean_nat_dec_lt(x_546, x_548);
if (x_549 == 0)
{
lean_object* x_550; 
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_518);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_1);
lean_ctor_set(x_550, 1, x_543);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_1);
x_551 = lean_nat_sub(x_548, x_546);
lean_dec(x_546);
lean_dec(x_548);
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_sub(x_551, x_552);
lean_dec(x_551);
x_554 = l_Lean_Expr_getRevArg_x21(x_518, x_553);
lean_dec(x_518);
x_1 = x_554;
x_6 = x_543;
goto _start;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_528);
lean_dec(x_518);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_556 = !lean_is_exclusive(x_522);
if (x_556 == 0)
{
lean_object* x_557; 
x_557 = lean_ctor_get(x_522, 0);
lean_dec(x_557);
lean_ctor_set(x_522, 0, x_1);
return x_522;
}
else
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_522, 1);
lean_inc(x_558);
lean_dec(x_522);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_1);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_518);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_522);
if (x_560 == 0)
{
return x_522;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_522, 0);
x_562 = lean_ctor_get(x_522, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_522);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
else
{
lean_dec(x_520);
lean_dec(x_518);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_516, 0, x_1);
return x_516;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_516, 0);
x_565 = lean_ctor_get(x_516, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_516);
x_566 = l_Lean_Expr_getAppFn(x_564);
if (lean_obj_tag(x_566) == 4)
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
lean_dec(x_566);
x_568 = l_Lean_Meta_getConst_x3f(x_567, x_2, x_3, x_4, x_5, x_565);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_564);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_571 = x_568;
} else {
 lean_dec_ref(x_568);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_1);
lean_ctor_set(x_572, 1, x_570);
return x_572;
}
else
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_569, 0);
lean_inc(x_573);
lean_dec(x_569);
if (lean_obj_tag(x_573) == 6)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_574 = lean_ctor_get(x_568, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_575 = x_568;
} else {
 lean_dec_ref(x_568);
 x_575 = lean_box(0);
}
x_576 = lean_ctor_get(x_573, 0);
lean_inc(x_576);
lean_dec(x_573);
x_577 = lean_ctor_get(x_576, 3);
lean_inc(x_577);
lean_dec(x_576);
x_578 = lean_nat_add(x_577, x_514);
lean_dec(x_514);
lean_dec(x_577);
x_579 = lean_unsigned_to_nat(0u);
x_580 = l_Lean_Expr_getAppNumArgsAux(x_564, x_579);
x_581 = lean_nat_dec_lt(x_578, x_580);
if (x_581 == 0)
{
lean_object* x_582; 
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_564);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_575)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_575;
}
lean_ctor_set(x_582, 0, x_1);
lean_ctor_set(x_582, 1, x_574);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec(x_575);
lean_dec(x_1);
x_583 = lean_nat_sub(x_580, x_578);
lean_dec(x_578);
lean_dec(x_580);
x_584 = lean_unsigned_to_nat(1u);
x_585 = lean_nat_sub(x_583, x_584);
lean_dec(x_583);
x_586 = l_Lean_Expr_getRevArg_x21(x_564, x_585);
lean_dec(x_564);
x_1 = x_586;
x_6 = x_574;
goto _start;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_573);
lean_dec(x_564);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_588 = lean_ctor_get(x_568, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_589 = x_568;
} else {
 lean_dec_ref(x_568);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_1);
lean_ctor_set(x_590, 1, x_588);
return x_590;
}
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_564);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_591 = lean_ctor_get(x_568, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_568, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_593 = x_568;
} else {
 lean_dec_ref(x_568);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
else
{
lean_object* x_595; 
lean_dec(x_566);
lean_dec(x_564);
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_1);
lean_ctor_set(x_595, 1, x_565);
return x_595;
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_514);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_596 = !lean_is_exclusive(x_516);
if (x_596 == 0)
{
return x_516;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_516, 0);
x_598 = lean_ctor_get(x_516, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_516);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
default: 
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_1);
x_600 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_601 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_602 = lean_panic_fn(x_600, x_601);
x_603 = lean_apply_5(x_602, x_2, x_3, x_4, x_5, x_345);
return x_603;
}
}
}
block_611:
{
if (x_605 == 0)
{
x_345 = x_606;
goto block_604;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_inc(x_1);
x_607 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_607, 0, x_1);
x_608 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_609 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_608, x_607, x_2, x_3, x_4, x_5, x_606);
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_345 = x_610;
goto block_604;
}
}
}
case 8:
{
lean_object* x_624; uint8_t x_884; lean_object* x_885; lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; 
x_891 = lean_st_ref_get(x_5, x_6);
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_892, 3);
lean_inc(x_893);
lean_dec(x_892);
x_894 = lean_ctor_get_uint8(x_893, sizeof(void*)*1);
lean_dec(x_893);
if (x_894 == 0)
{
lean_object* x_895; uint8_t x_896; 
x_895 = lean_ctor_get(x_891, 1);
lean_inc(x_895);
lean_dec(x_891);
x_896 = 0;
x_884 = x_896;
x_885 = x_895;
goto block_890;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; 
x_897 = lean_ctor_get(x_891, 1);
lean_inc(x_897);
lean_dec(x_891);
x_898 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_899 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_898, x_2, x_3, x_4, x_5, x_897);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
lean_dec(x_899);
x_902 = lean_unbox(x_900);
lean_dec(x_900);
x_884 = x_902;
x_885 = x_901;
goto block_890;
}
block_883:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_625; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_1);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
case 5:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_1, 0);
lean_inc(x_626);
x_627 = l_Lean_Expr_getAppFn(x_626);
lean_dec(x_626);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_627);
x_628 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_627, x_2, x_3, x_4, x_5, x_624);
if (lean_obj_tag(x_628) == 0)
{
uint8_t x_629; 
x_629 = !lean_is_exclusive(x_628);
if (x_629 == 0)
{
lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_630 = lean_ctor_get(x_628, 0);
x_631 = lean_ctor_get(x_628, 1);
x_632 = l_Lean_Expr_isLambda(x_630);
if (x_632 == 0)
{
if (lean_obj_tag(x_630) == 4)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_free_object(x_628);
x_633 = lean_ctor_get(x_630, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_630, 1);
lean_inc(x_634);
lean_inc(x_1);
lean_inc(x_630);
lean_inc(x_627);
x_635 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_635, 0, x_627);
lean_closure_set(x_635, 1, x_630);
lean_closure_set(x_635, 2, x_1);
x_636 = l_Lean_Meta_getConst_x3f(x_633, x_2, x_3, x_4, x_5, x_631);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
if (lean_obj_tag(x_637) == 0)
{
uint8_t x_638; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_638 = !lean_is_exclusive(x_636);
if (x_638 == 0)
{
lean_object* x_639; uint8_t x_640; 
x_639 = lean_ctor_get(x_636, 0);
lean_dec(x_639);
x_640 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_640 == 0)
{
lean_object* x_641; 
x_641 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
lean_ctor_set(x_636, 0, x_641);
return x_636;
}
else
{
lean_dec(x_630);
lean_ctor_set(x_636, 0, x_1);
return x_636;
}
}
else
{
lean_object* x_642; uint8_t x_643; 
x_642 = lean_ctor_get(x_636, 1);
lean_inc(x_642);
lean_dec(x_636);
x_643 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; 
x_644 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_642);
return x_645;
}
else
{
lean_object* x_646; 
lean_dec(x_630);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_1);
lean_ctor_set(x_646, 1, x_642);
return x_646;
}
}
}
else
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_637, 0);
lean_inc(x_647);
lean_dec(x_637);
switch (lean_obj_tag(x_647)) {
case 1:
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; 
lean_dec(x_635);
x_648 = lean_ctor_get(x_636, 1);
lean_inc(x_648);
lean_dec(x_636);
x_649 = l_Lean_ConstantInfo_name(x_647);
x_650 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_649, x_2, x_3, x_4, x_5, x_648);
lean_dec(x_649);
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_unbox(x_651);
lean_dec(x_651);
if (x_652 == 0)
{
uint8_t x_653; 
lean_dec(x_647);
lean_dec(x_634);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_653 = !lean_is_exclusive(x_650);
if (x_653 == 0)
{
lean_object* x_654; uint8_t x_655; 
x_654 = lean_ctor_get(x_650, 0);
lean_dec(x_654);
x_655 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_655 == 0)
{
lean_object* x_656; 
x_656 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
lean_ctor_set(x_650, 0, x_656);
return x_650;
}
else
{
lean_dec(x_630);
lean_ctor_set(x_650, 0, x_1);
return x_650;
}
}
else
{
lean_object* x_657; uint8_t x_658; 
x_657 = lean_ctor_get(x_650, 1);
lean_inc(x_657);
lean_dec(x_650);
x_658 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_657);
return x_660;
}
else
{
lean_object* x_661; 
lean_dec(x_630);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_1);
lean_ctor_set(x_661, 1, x_657);
return x_661;
}
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_662 = lean_ctor_get(x_650, 1);
lean_inc(x_662);
lean_dec(x_650);
x_663 = lean_unsigned_to_nat(0u);
x_664 = l_Lean_Expr_getAppNumArgsAux(x_1, x_663);
x_665 = lean_mk_empty_array_with_capacity(x_664);
lean_dec(x_664);
lean_inc(x_1);
x_666 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_665);
x_667 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_627, x_630, x_647, x_634, x_666, x_2, x_3, x_4, x_5, x_662);
lean_dec(x_666);
lean_dec(x_634);
lean_dec(x_647);
lean_dec(x_630);
lean_dec(x_627);
return x_667;
}
}
case 4:
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_630);
lean_dec(x_627);
x_668 = lean_ctor_get(x_636, 1);
lean_inc(x_668);
lean_dec(x_636);
x_669 = lean_ctor_get(x_647, 0);
lean_inc(x_669);
lean_dec(x_647);
x_670 = lean_unsigned_to_nat(0u);
x_671 = l_Lean_Expr_getAppNumArgsAux(x_1, x_670);
x_672 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_671);
x_673 = lean_mk_array(x_671, x_672);
x_674 = lean_unsigned_to_nat(1u);
x_675 = lean_nat_sub(x_671, x_674);
lean_dec(x_671);
x_676 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_673, x_675);
x_677 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_678 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_669, x_634, x_676, x_635, x_677, x_2, x_3, x_4, x_5, x_668);
lean_dec(x_676);
lean_dec(x_634);
lean_dec(x_669);
return x_678;
}
case 7:
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_630);
lean_dec(x_627);
x_679 = lean_ctor_get(x_636, 1);
lean_inc(x_679);
lean_dec(x_636);
x_680 = lean_ctor_get(x_647, 0);
lean_inc(x_680);
lean_dec(x_647);
x_681 = lean_unsigned_to_nat(0u);
x_682 = l_Lean_Expr_getAppNumArgsAux(x_1, x_681);
x_683 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_682);
x_684 = lean_mk_array(x_682, x_683);
x_685 = lean_unsigned_to_nat(1u);
x_686 = lean_nat_sub(x_682, x_685);
lean_dec(x_682);
x_687 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_684, x_686);
x_688 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_689 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_680, x_634, x_687, x_635, x_688, x_2, x_3, x_4, x_5, x_679);
lean_dec(x_687);
lean_dec(x_634);
return x_689;
}
default: 
{
uint8_t x_690; 
lean_dec(x_647);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_690 = !lean_is_exclusive(x_636);
if (x_690 == 0)
{
lean_object* x_691; uint8_t x_692; 
x_691 = lean_ctor_get(x_636, 0);
lean_dec(x_691);
x_692 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_692 == 0)
{
lean_object* x_693; 
x_693 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
lean_ctor_set(x_636, 0, x_693);
return x_636;
}
else
{
lean_dec(x_630);
lean_ctor_set(x_636, 0, x_1);
return x_636;
}
}
else
{
lean_object* x_694; uint8_t x_695; 
x_694 = lean_ctor_get(x_636, 1);
lean_inc(x_694);
lean_dec(x_636);
x_695 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; 
x_696 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
x_697 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_694);
return x_697;
}
else
{
lean_object* x_698; 
lean_dec(x_630);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_1);
lean_ctor_set(x_698, 1, x_694);
return x_698;
}
}
}
}
}
}
else
{
uint8_t x_699; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_630);
lean_dec(x_627);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_699 = !lean_is_exclusive(x_636);
if (x_699 == 0)
{
return x_636;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_636, 0);
x_701 = lean_ctor_get(x_636, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_636);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
}
else
{
uint8_t x_703; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_703 = lean_expr_eqv(x_627, x_630);
lean_dec(x_627);
if (x_703 == 0)
{
lean_object* x_704; 
x_704 = l_Lean_Expr_updateFn(x_1, x_630);
lean_dec(x_630);
lean_ctor_set(x_628, 0, x_704);
return x_628;
}
else
{
lean_dec(x_630);
lean_ctor_set(x_628, 0, x_1);
return x_628;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_free_object(x_628);
lean_dec(x_627);
x_705 = lean_unsigned_to_nat(0u);
x_706 = l_Lean_Expr_getAppNumArgsAux(x_1, x_705);
x_707 = lean_mk_empty_array_with_capacity(x_706);
lean_dec(x_706);
x_708 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_707);
x_709 = l_Lean_Expr_betaRev(x_630, x_708);
lean_dec(x_708);
lean_dec(x_630);
x_1 = x_709;
x_6 = x_631;
goto _start;
}
}
else
{
lean_object* x_711; lean_object* x_712; uint8_t x_713; 
x_711 = lean_ctor_get(x_628, 0);
x_712 = lean_ctor_get(x_628, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_628);
x_713 = l_Lean_Expr_isLambda(x_711);
if (x_713 == 0)
{
if (lean_obj_tag(x_711) == 4)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_714 = lean_ctor_get(x_711, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_711, 1);
lean_inc(x_715);
lean_inc(x_1);
lean_inc(x_711);
lean_inc(x_627);
x_716 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_716, 0, x_627);
lean_closure_set(x_716, 1, x_711);
lean_closure_set(x_716, 2, x_1);
x_717 = l_Lean_Meta_getConst_x3f(x_714, x_2, x_3, x_4, x_5, x_712);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; uint8_t x_721; 
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_720 = x_717;
} else {
 lean_dec_ref(x_717);
 x_720 = lean_box(0);
}
x_721 = lean_expr_eqv(x_627, x_711);
lean_dec(x_627);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; 
x_722 = l_Lean_Expr_updateFn(x_1, x_711);
lean_dec(x_711);
if (lean_is_scalar(x_720)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_720;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_719);
return x_723;
}
else
{
lean_object* x_724; 
lean_dec(x_711);
if (lean_is_scalar(x_720)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_720;
}
lean_ctor_set(x_724, 0, x_1);
lean_ctor_set(x_724, 1, x_719);
return x_724;
}
}
else
{
lean_object* x_725; 
x_725 = lean_ctor_get(x_718, 0);
lean_inc(x_725);
lean_dec(x_718);
switch (lean_obj_tag(x_725)) {
case 1:
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; 
lean_dec(x_716);
x_726 = lean_ctor_get(x_717, 1);
lean_inc(x_726);
lean_dec(x_717);
x_727 = l_Lean_ConstantInfo_name(x_725);
x_728 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_727, x_2, x_3, x_4, x_5, x_726);
lean_dec(x_727);
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_unbox(x_729);
lean_dec(x_729);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; uint8_t x_733; 
lean_dec(x_725);
lean_dec(x_715);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_731 = lean_ctor_get(x_728, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_732 = x_728;
} else {
 lean_dec_ref(x_728);
 x_732 = lean_box(0);
}
x_733 = lean_expr_eqv(x_627, x_711);
lean_dec(x_627);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; 
x_734 = l_Lean_Expr_updateFn(x_1, x_711);
lean_dec(x_711);
if (lean_is_scalar(x_732)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_732;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_731);
return x_735;
}
else
{
lean_object* x_736; 
lean_dec(x_711);
if (lean_is_scalar(x_732)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_732;
}
lean_ctor_set(x_736, 0, x_1);
lean_ctor_set(x_736, 1, x_731);
return x_736;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_737 = lean_ctor_get(x_728, 1);
lean_inc(x_737);
lean_dec(x_728);
x_738 = lean_unsigned_to_nat(0u);
x_739 = l_Lean_Expr_getAppNumArgsAux(x_1, x_738);
x_740 = lean_mk_empty_array_with_capacity(x_739);
lean_dec(x_739);
lean_inc(x_1);
x_741 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_740);
x_742 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_627, x_711, x_725, x_715, x_741, x_2, x_3, x_4, x_5, x_737);
lean_dec(x_741);
lean_dec(x_715);
lean_dec(x_725);
lean_dec(x_711);
lean_dec(x_627);
return x_742;
}
}
case 4:
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_711);
lean_dec(x_627);
x_743 = lean_ctor_get(x_717, 1);
lean_inc(x_743);
lean_dec(x_717);
x_744 = lean_ctor_get(x_725, 0);
lean_inc(x_744);
lean_dec(x_725);
x_745 = lean_unsigned_to_nat(0u);
x_746 = l_Lean_Expr_getAppNumArgsAux(x_1, x_745);
x_747 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_746);
x_748 = lean_mk_array(x_746, x_747);
x_749 = lean_unsigned_to_nat(1u);
x_750 = lean_nat_sub(x_746, x_749);
lean_dec(x_746);
x_751 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_748, x_750);
x_752 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_753 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_744, x_715, x_751, x_716, x_752, x_2, x_3, x_4, x_5, x_743);
lean_dec(x_751);
lean_dec(x_715);
lean_dec(x_744);
return x_753;
}
case 7:
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_711);
lean_dec(x_627);
x_754 = lean_ctor_get(x_717, 1);
lean_inc(x_754);
lean_dec(x_717);
x_755 = lean_ctor_get(x_725, 0);
lean_inc(x_755);
lean_dec(x_725);
x_756 = lean_unsigned_to_nat(0u);
x_757 = l_Lean_Expr_getAppNumArgsAux(x_1, x_756);
x_758 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_757);
x_759 = lean_mk_array(x_757, x_758);
x_760 = lean_unsigned_to_nat(1u);
x_761 = lean_nat_sub(x_757, x_760);
lean_dec(x_757);
x_762 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_759, x_761);
x_763 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_764 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_755, x_715, x_762, x_716, x_763, x_2, x_3, x_4, x_5, x_754);
lean_dec(x_762);
lean_dec(x_715);
return x_764;
}
default: 
{
lean_object* x_765; lean_object* x_766; uint8_t x_767; 
lean_dec(x_725);
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_765 = lean_ctor_get(x_717, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_766 = x_717;
} else {
 lean_dec_ref(x_717);
 x_766 = lean_box(0);
}
x_767 = lean_expr_eqv(x_627, x_711);
lean_dec(x_627);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; 
x_768 = l_Lean_Expr_updateFn(x_1, x_711);
lean_dec(x_711);
if (lean_is_scalar(x_766)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_766;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_765);
return x_769;
}
else
{
lean_object* x_770; 
lean_dec(x_711);
if (lean_is_scalar(x_766)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_766;
}
lean_ctor_set(x_770, 0, x_1);
lean_ctor_set(x_770, 1, x_765);
return x_770;
}
}
}
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_711);
lean_dec(x_627);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_771 = lean_ctor_get(x_717, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_717, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_773 = x_717;
} else {
 lean_dec_ref(x_717);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 2, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_771);
lean_ctor_set(x_774, 1, x_772);
return x_774;
}
}
else
{
uint8_t x_775; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_775 = lean_expr_eqv(x_627, x_711);
lean_dec(x_627);
if (x_775 == 0)
{
lean_object* x_776; lean_object* x_777; 
x_776 = l_Lean_Expr_updateFn(x_1, x_711);
lean_dec(x_711);
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_712);
return x_777;
}
else
{
lean_object* x_778; 
lean_dec(x_711);
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_1);
lean_ctor_set(x_778, 1, x_712);
return x_778;
}
}
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_627);
x_779 = lean_unsigned_to_nat(0u);
x_780 = l_Lean_Expr_getAppNumArgsAux(x_1, x_779);
x_781 = lean_mk_empty_array_with_capacity(x_780);
lean_dec(x_780);
x_782 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_781);
x_783 = l_Lean_Expr_betaRev(x_711, x_782);
lean_dec(x_782);
lean_dec(x_711);
x_1 = x_783;
x_6 = x_712;
goto _start;
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_627);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_785 = !lean_is_exclusive(x_628);
if (x_785 == 0)
{
return x_628;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_628, 0);
x_787 = lean_ctor_get(x_628, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_628);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
case 8:
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_1, 2);
lean_inc(x_789);
x_790 = lean_ctor_get(x_1, 3);
lean_inc(x_790);
lean_dec(x_1);
x_791 = lean_expr_instantiate1(x_790, x_789);
lean_dec(x_789);
lean_dec(x_790);
x_1 = x_791;
x_6 = x_624;
goto _start;
}
case 11:
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_793 = lean_ctor_get(x_1, 1);
lean_inc(x_793);
x_794 = lean_ctor_get(x_1, 2);
lean_inc(x_794);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_795 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_794, x_2, x_3, x_4, x_5, x_624);
if (lean_obj_tag(x_795) == 0)
{
uint8_t x_796; 
x_796 = !lean_is_exclusive(x_795);
if (x_796 == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_795, 0);
x_798 = lean_ctor_get(x_795, 1);
x_799 = l_Lean_Expr_getAppFn(x_797);
if (lean_obj_tag(x_799) == 4)
{
lean_object* x_800; lean_object* x_801; 
lean_free_object(x_795);
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
lean_dec(x_799);
x_801 = l_Lean_Meta_getConst_x3f(x_800, x_2, x_3, x_4, x_5, x_798);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
if (lean_obj_tag(x_802) == 0)
{
uint8_t x_803; 
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_803 = !lean_is_exclusive(x_801);
if (x_803 == 0)
{
lean_object* x_804; 
x_804 = lean_ctor_get(x_801, 0);
lean_dec(x_804);
lean_ctor_set(x_801, 0, x_1);
return x_801;
}
else
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_801, 1);
lean_inc(x_805);
lean_dec(x_801);
x_806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_806, 0, x_1);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
else
{
lean_object* x_807; 
x_807 = lean_ctor_get(x_802, 0);
lean_inc(x_807);
lean_dec(x_802);
if (lean_obj_tag(x_807) == 6)
{
uint8_t x_808; 
x_808 = !lean_is_exclusive(x_801);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; uint8_t x_816; 
x_809 = lean_ctor_get(x_801, 1);
x_810 = lean_ctor_get(x_801, 0);
lean_dec(x_810);
x_811 = lean_ctor_get(x_807, 0);
lean_inc(x_811);
lean_dec(x_807);
x_812 = lean_ctor_get(x_811, 3);
lean_inc(x_812);
lean_dec(x_811);
x_813 = lean_nat_add(x_812, x_793);
lean_dec(x_793);
lean_dec(x_812);
x_814 = lean_unsigned_to_nat(0u);
x_815 = l_Lean_Expr_getAppNumArgsAux(x_797, x_814);
x_816 = lean_nat_dec_lt(x_813, x_815);
if (x_816 == 0)
{
lean_dec(x_815);
lean_dec(x_813);
lean_dec(x_797);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_801, 0, x_1);
return x_801;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_free_object(x_801);
lean_dec(x_1);
x_817 = lean_nat_sub(x_815, x_813);
lean_dec(x_813);
lean_dec(x_815);
x_818 = lean_unsigned_to_nat(1u);
x_819 = lean_nat_sub(x_817, x_818);
lean_dec(x_817);
x_820 = l_Lean_Expr_getRevArg_x21(x_797, x_819);
lean_dec(x_797);
x_1 = x_820;
x_6 = x_809;
goto _start;
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; 
x_822 = lean_ctor_get(x_801, 1);
lean_inc(x_822);
lean_dec(x_801);
x_823 = lean_ctor_get(x_807, 0);
lean_inc(x_823);
lean_dec(x_807);
x_824 = lean_ctor_get(x_823, 3);
lean_inc(x_824);
lean_dec(x_823);
x_825 = lean_nat_add(x_824, x_793);
lean_dec(x_793);
lean_dec(x_824);
x_826 = lean_unsigned_to_nat(0u);
x_827 = l_Lean_Expr_getAppNumArgsAux(x_797, x_826);
x_828 = lean_nat_dec_lt(x_825, x_827);
if (x_828 == 0)
{
lean_object* x_829; 
lean_dec(x_827);
lean_dec(x_825);
lean_dec(x_797);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_829, 0, x_1);
lean_ctor_set(x_829, 1, x_822);
return x_829;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_1);
x_830 = lean_nat_sub(x_827, x_825);
lean_dec(x_825);
lean_dec(x_827);
x_831 = lean_unsigned_to_nat(1u);
x_832 = lean_nat_sub(x_830, x_831);
lean_dec(x_830);
x_833 = l_Lean_Expr_getRevArg_x21(x_797, x_832);
lean_dec(x_797);
x_1 = x_833;
x_6 = x_822;
goto _start;
}
}
}
else
{
uint8_t x_835; 
lean_dec(x_807);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_835 = !lean_is_exclusive(x_801);
if (x_835 == 0)
{
lean_object* x_836; 
x_836 = lean_ctor_get(x_801, 0);
lean_dec(x_836);
lean_ctor_set(x_801, 0, x_1);
return x_801;
}
else
{
lean_object* x_837; lean_object* x_838; 
x_837 = lean_ctor_get(x_801, 1);
lean_inc(x_837);
lean_dec(x_801);
x_838 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_838, 0, x_1);
lean_ctor_set(x_838, 1, x_837);
return x_838;
}
}
}
}
else
{
uint8_t x_839; 
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_839 = !lean_is_exclusive(x_801);
if (x_839 == 0)
{
return x_801;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_801, 0);
x_841 = lean_ctor_get(x_801, 1);
lean_inc(x_841);
lean_inc(x_840);
lean_dec(x_801);
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_840);
lean_ctor_set(x_842, 1, x_841);
return x_842;
}
}
}
else
{
lean_dec(x_799);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_795, 0, x_1);
return x_795;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_795, 0);
x_844 = lean_ctor_get(x_795, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_795);
x_845 = l_Lean_Expr_getAppFn(x_843);
if (lean_obj_tag(x_845) == 4)
{
lean_object* x_846; lean_object* x_847; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
lean_dec(x_845);
x_847 = l_Lean_Meta_getConst_x3f(x_846, x_2, x_3, x_4, x_5, x_844);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_843);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_850 = x_847;
} else {
 lean_dec_ref(x_847);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_1);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
else
{
lean_object* x_852; 
x_852 = lean_ctor_get(x_848, 0);
lean_inc(x_852);
lean_dec(x_848);
if (lean_obj_tag(x_852) == 6)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_853 = lean_ctor_get(x_847, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_854 = x_847;
} else {
 lean_dec_ref(x_847);
 x_854 = lean_box(0);
}
x_855 = lean_ctor_get(x_852, 0);
lean_inc(x_855);
lean_dec(x_852);
x_856 = lean_ctor_get(x_855, 3);
lean_inc(x_856);
lean_dec(x_855);
x_857 = lean_nat_add(x_856, x_793);
lean_dec(x_793);
lean_dec(x_856);
x_858 = lean_unsigned_to_nat(0u);
x_859 = l_Lean_Expr_getAppNumArgsAux(x_843, x_858);
x_860 = lean_nat_dec_lt(x_857, x_859);
if (x_860 == 0)
{
lean_object* x_861; 
lean_dec(x_859);
lean_dec(x_857);
lean_dec(x_843);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_854)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_854;
}
lean_ctor_set(x_861, 0, x_1);
lean_ctor_set(x_861, 1, x_853);
return x_861;
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_854);
lean_dec(x_1);
x_862 = lean_nat_sub(x_859, x_857);
lean_dec(x_857);
lean_dec(x_859);
x_863 = lean_unsigned_to_nat(1u);
x_864 = lean_nat_sub(x_862, x_863);
lean_dec(x_862);
x_865 = l_Lean_Expr_getRevArg_x21(x_843, x_864);
lean_dec(x_843);
x_1 = x_865;
x_6 = x_853;
goto _start;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_852);
lean_dec(x_843);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_867 = lean_ctor_get(x_847, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_868 = x_847;
} else {
 lean_dec_ref(x_847);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_1);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_843);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_870 = lean_ctor_get(x_847, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_847, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_872 = x_847;
} else {
 lean_dec_ref(x_847);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_871);
return x_873;
}
}
else
{
lean_object* x_874; 
lean_dec(x_845);
lean_dec(x_843);
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_874 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_874, 0, x_1);
lean_ctor_set(x_874, 1, x_844);
return x_874;
}
}
}
else
{
uint8_t x_875; 
lean_dec(x_793);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_875 = !lean_is_exclusive(x_795);
if (x_875 == 0)
{
return x_795;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_795, 0);
x_877 = lean_ctor_get(x_795, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_795);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
return x_878;
}
}
}
default: 
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_1);
x_879 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_880 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_881 = lean_panic_fn(x_879, x_880);
x_882 = lean_apply_5(x_881, x_2, x_3, x_4, x_5, x_624);
return x_882;
}
}
}
block_890:
{
if (x_884 == 0)
{
x_624 = x_885;
goto block_883;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_inc(x_1);
x_886 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_886, 0, x_1);
x_887 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_888 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_887, x_886, x_2, x_3, x_4, x_5, x_885);
x_889 = lean_ctor_get(x_888, 1);
lean_inc(x_889);
lean_dec(x_888);
x_624 = x_889;
goto block_883;
}
}
}
case 10:
{
lean_object* x_903; 
x_903 = lean_ctor_get(x_1, 1);
lean_inc(x_903);
lean_dec(x_1);
x_1 = x_903;
goto _start;
}
case 11:
{
lean_object* x_905; uint8_t x_1165; lean_object* x_1166; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
x_1172 = lean_st_ref_get(x_5, x_6);
x_1173 = lean_ctor_get(x_1172, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1173, 3);
lean_inc(x_1174);
lean_dec(x_1173);
x_1175 = lean_ctor_get_uint8(x_1174, sizeof(void*)*1);
lean_dec(x_1174);
if (x_1175 == 0)
{
lean_object* x_1176; uint8_t x_1177; 
x_1176 = lean_ctor_get(x_1172, 1);
lean_inc(x_1176);
lean_dec(x_1172);
x_1177 = 0;
x_1165 = x_1177;
x_1166 = x_1176;
goto block_1171;
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
x_1178 = lean_ctor_get(x_1172, 1);
lean_inc(x_1178);
lean_dec(x_1172);
x_1179 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_1180 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_1179, x_2, x_3, x_4, x_5, x_1178);
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
lean_dec(x_1180);
x_1183 = lean_unbox(x_1181);
lean_dec(x_1181);
x_1165 = x_1183;
x_1166 = x_1182;
goto block_1171;
}
block_1164:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_906; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_906 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_906, 0, x_1);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
case 5:
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_1, 0);
lean_inc(x_907);
x_908 = l_Lean_Expr_getAppFn(x_907);
lean_dec(x_907);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_908);
x_909 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_908, x_2, x_3, x_4, x_5, x_905);
if (lean_obj_tag(x_909) == 0)
{
uint8_t x_910; 
x_910 = !lean_is_exclusive(x_909);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; uint8_t x_913; 
x_911 = lean_ctor_get(x_909, 0);
x_912 = lean_ctor_get(x_909, 1);
x_913 = l_Lean_Expr_isLambda(x_911);
if (x_913 == 0)
{
if (lean_obj_tag(x_911) == 4)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_free_object(x_909);
x_914 = lean_ctor_get(x_911, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_911, 1);
lean_inc(x_915);
lean_inc(x_1);
lean_inc(x_911);
lean_inc(x_908);
x_916 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_916, 0, x_908);
lean_closure_set(x_916, 1, x_911);
lean_closure_set(x_916, 2, x_1);
x_917 = l_Lean_Meta_getConst_x3f(x_914, x_2, x_3, x_4, x_5, x_912);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
if (lean_obj_tag(x_918) == 0)
{
uint8_t x_919; 
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_919 = !lean_is_exclusive(x_917);
if (x_919 == 0)
{
lean_object* x_920; uint8_t x_921; 
x_920 = lean_ctor_get(x_917, 0);
lean_dec(x_920);
x_921 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_921 == 0)
{
lean_object* x_922; 
x_922 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
lean_ctor_set(x_917, 0, x_922);
return x_917;
}
else
{
lean_dec(x_911);
lean_ctor_set(x_917, 0, x_1);
return x_917;
}
}
else
{
lean_object* x_923; uint8_t x_924; 
x_923 = lean_ctor_get(x_917, 1);
lean_inc(x_923);
lean_dec(x_917);
x_924 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_924 == 0)
{
lean_object* x_925; lean_object* x_926; 
x_925 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
x_926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_923);
return x_926;
}
else
{
lean_object* x_927; 
lean_dec(x_911);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_1);
lean_ctor_set(x_927, 1, x_923);
return x_927;
}
}
}
else
{
lean_object* x_928; 
x_928 = lean_ctor_get(x_918, 0);
lean_inc(x_928);
lean_dec(x_918);
switch (lean_obj_tag(x_928)) {
case 1:
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; uint8_t x_933; 
lean_dec(x_916);
x_929 = lean_ctor_get(x_917, 1);
lean_inc(x_929);
lean_dec(x_917);
x_930 = l_Lean_ConstantInfo_name(x_928);
x_931 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_930, x_2, x_3, x_4, x_5, x_929);
lean_dec(x_930);
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_unbox(x_932);
lean_dec(x_932);
if (x_933 == 0)
{
uint8_t x_934; 
lean_dec(x_928);
lean_dec(x_915);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_934 = !lean_is_exclusive(x_931);
if (x_934 == 0)
{
lean_object* x_935; uint8_t x_936; 
x_935 = lean_ctor_get(x_931, 0);
lean_dec(x_935);
x_936 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_936 == 0)
{
lean_object* x_937; 
x_937 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
lean_ctor_set(x_931, 0, x_937);
return x_931;
}
else
{
lean_dec(x_911);
lean_ctor_set(x_931, 0, x_1);
return x_931;
}
}
else
{
lean_object* x_938; uint8_t x_939; 
x_938 = lean_ctor_get(x_931, 1);
lean_inc(x_938);
lean_dec(x_931);
x_939 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; 
x_940 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
x_941 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_938);
return x_941;
}
else
{
lean_object* x_942; 
lean_dec(x_911);
x_942 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_942, 0, x_1);
lean_ctor_set(x_942, 1, x_938);
return x_942;
}
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_943 = lean_ctor_get(x_931, 1);
lean_inc(x_943);
lean_dec(x_931);
x_944 = lean_unsigned_to_nat(0u);
x_945 = l_Lean_Expr_getAppNumArgsAux(x_1, x_944);
x_946 = lean_mk_empty_array_with_capacity(x_945);
lean_dec(x_945);
lean_inc(x_1);
x_947 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_946);
x_948 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_908, x_911, x_928, x_915, x_947, x_2, x_3, x_4, x_5, x_943);
lean_dec(x_947);
lean_dec(x_915);
lean_dec(x_928);
lean_dec(x_911);
lean_dec(x_908);
return x_948;
}
}
case 4:
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_911);
lean_dec(x_908);
x_949 = lean_ctor_get(x_917, 1);
lean_inc(x_949);
lean_dec(x_917);
x_950 = lean_ctor_get(x_928, 0);
lean_inc(x_950);
lean_dec(x_928);
x_951 = lean_unsigned_to_nat(0u);
x_952 = l_Lean_Expr_getAppNumArgsAux(x_1, x_951);
x_953 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_952);
x_954 = lean_mk_array(x_952, x_953);
x_955 = lean_unsigned_to_nat(1u);
x_956 = lean_nat_sub(x_952, x_955);
lean_dec(x_952);
x_957 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_954, x_956);
x_958 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_959 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_950, x_915, x_957, x_916, x_958, x_2, x_3, x_4, x_5, x_949);
lean_dec(x_957);
lean_dec(x_915);
lean_dec(x_950);
return x_959;
}
case 7:
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_911);
lean_dec(x_908);
x_960 = lean_ctor_get(x_917, 1);
lean_inc(x_960);
lean_dec(x_917);
x_961 = lean_ctor_get(x_928, 0);
lean_inc(x_961);
lean_dec(x_928);
x_962 = lean_unsigned_to_nat(0u);
x_963 = l_Lean_Expr_getAppNumArgsAux(x_1, x_962);
x_964 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_963);
x_965 = lean_mk_array(x_963, x_964);
x_966 = lean_unsigned_to_nat(1u);
x_967 = lean_nat_sub(x_963, x_966);
lean_dec(x_963);
x_968 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_965, x_967);
x_969 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_970 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_961, x_915, x_968, x_916, x_969, x_2, x_3, x_4, x_5, x_960);
lean_dec(x_968);
lean_dec(x_915);
return x_970;
}
default: 
{
uint8_t x_971; 
lean_dec(x_928);
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_971 = !lean_is_exclusive(x_917);
if (x_971 == 0)
{
lean_object* x_972; uint8_t x_973; 
x_972 = lean_ctor_get(x_917, 0);
lean_dec(x_972);
x_973 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_973 == 0)
{
lean_object* x_974; 
x_974 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
lean_ctor_set(x_917, 0, x_974);
return x_917;
}
else
{
lean_dec(x_911);
lean_ctor_set(x_917, 0, x_1);
return x_917;
}
}
else
{
lean_object* x_975; uint8_t x_976; 
x_975 = lean_ctor_get(x_917, 1);
lean_inc(x_975);
lean_dec(x_917);
x_976 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_976 == 0)
{
lean_object* x_977; lean_object* x_978; 
x_977 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
x_978 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_975);
return x_978;
}
else
{
lean_object* x_979; 
lean_dec(x_911);
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_1);
lean_ctor_set(x_979, 1, x_975);
return x_979;
}
}
}
}
}
}
else
{
uint8_t x_980; 
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_911);
lean_dec(x_908);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_980 = !lean_is_exclusive(x_917);
if (x_980 == 0)
{
return x_917;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_917, 0);
x_982 = lean_ctor_get(x_917, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_917);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
else
{
uint8_t x_984; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_984 = lean_expr_eqv(x_908, x_911);
lean_dec(x_908);
if (x_984 == 0)
{
lean_object* x_985; 
x_985 = l_Lean_Expr_updateFn(x_1, x_911);
lean_dec(x_911);
lean_ctor_set(x_909, 0, x_985);
return x_909;
}
else
{
lean_dec(x_911);
lean_ctor_set(x_909, 0, x_1);
return x_909;
}
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_free_object(x_909);
lean_dec(x_908);
x_986 = lean_unsigned_to_nat(0u);
x_987 = l_Lean_Expr_getAppNumArgsAux(x_1, x_986);
x_988 = lean_mk_empty_array_with_capacity(x_987);
lean_dec(x_987);
x_989 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_988);
x_990 = l_Lean_Expr_betaRev(x_911, x_989);
lean_dec(x_989);
lean_dec(x_911);
x_1 = x_990;
x_6 = x_912;
goto _start;
}
}
else
{
lean_object* x_992; lean_object* x_993; uint8_t x_994; 
x_992 = lean_ctor_get(x_909, 0);
x_993 = lean_ctor_get(x_909, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_909);
x_994 = l_Lean_Expr_isLambda(x_992);
if (x_994 == 0)
{
if (lean_obj_tag(x_992) == 4)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_995 = lean_ctor_get(x_992, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_992, 1);
lean_inc(x_996);
lean_inc(x_1);
lean_inc(x_992);
lean_inc(x_908);
x_997 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_997, 0, x_908);
lean_closure_set(x_997, 1, x_992);
lean_closure_set(x_997, 2, x_1);
x_998 = l_Lean_Meta_getConst_x3f(x_995, x_2, x_3, x_4, x_5, x_993);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; uint8_t x_1002; 
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1001 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1001 = lean_box(0);
}
x_1002 = lean_expr_eqv(x_908, x_992);
lean_dec(x_908);
if (x_1002 == 0)
{
lean_object* x_1003; lean_object* x_1004; 
x_1003 = l_Lean_Expr_updateFn(x_1, x_992);
lean_dec(x_992);
if (lean_is_scalar(x_1001)) {
 x_1004 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1004 = x_1001;
}
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1000);
return x_1004;
}
else
{
lean_object* x_1005; 
lean_dec(x_992);
if (lean_is_scalar(x_1001)) {
 x_1005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1005 = x_1001;
}
lean_ctor_set(x_1005, 0, x_1);
lean_ctor_set(x_1005, 1, x_1000);
return x_1005;
}
}
else
{
lean_object* x_1006; 
x_1006 = lean_ctor_get(x_999, 0);
lean_inc(x_1006);
lean_dec(x_999);
switch (lean_obj_tag(x_1006)) {
case 1:
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; uint8_t x_1011; 
lean_dec(x_997);
x_1007 = lean_ctor_get(x_998, 1);
lean_inc(x_1007);
lean_dec(x_998);
x_1008 = l_Lean_ConstantInfo_name(x_1006);
x_1009 = l___private_Lean_Meta_WHNF_0__Lean_Meta_isAuxDefImp_x3f(x_1008, x_2, x_3, x_4, x_5, x_1007);
lean_dec(x_1008);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_unbox(x_1010);
lean_dec(x_1010);
if (x_1011 == 0)
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1012 = lean_ctor_get(x_1009, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1013 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1013 = lean_box(0);
}
x_1014 = lean_expr_eqv(x_908, x_992);
lean_dec(x_908);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; 
x_1015 = l_Lean_Expr_updateFn(x_1, x_992);
lean_dec(x_992);
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
lean_dec(x_992);
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
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1018 = lean_ctor_get(x_1009, 1);
lean_inc(x_1018);
lean_dec(x_1009);
x_1019 = lean_unsigned_to_nat(0u);
x_1020 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1019);
x_1021 = lean_mk_empty_array_with_capacity(x_1020);
lean_dec(x_1020);
lean_inc(x_1);
x_1022 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_1021);
x_1023 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__1(x_1, x_908, x_992, x_1006, x_996, x_1022, x_2, x_3, x_4, x_5, x_1018);
lean_dec(x_1022);
lean_dec(x_996);
lean_dec(x_1006);
lean_dec(x_992);
lean_dec(x_908);
return x_1023;
}
}
case 4:
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_992);
lean_dec(x_908);
x_1024 = lean_ctor_get(x_998, 1);
lean_inc(x_1024);
lean_dec(x_998);
x_1025 = lean_ctor_get(x_1006, 0);
lean_inc(x_1025);
lean_dec(x_1006);
x_1026 = lean_unsigned_to_nat(0u);
x_1027 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1026);
x_1028 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1027);
x_1029 = lean_mk_array(x_1027, x_1028);
x_1030 = lean_unsigned_to_nat(1u);
x_1031 = lean_nat_sub(x_1027, x_1030);
lean_dec(x_1027);
x_1032 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_1029, x_1031);
x_1033 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_1034 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceQuotRec___rarg(x_1025, x_996, x_1032, x_997, x_1033, x_2, x_3, x_4, x_5, x_1024);
lean_dec(x_1032);
lean_dec(x_996);
lean_dec(x_1025);
return x_1034;
}
case 7:
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec(x_992);
lean_dec(x_908);
x_1035 = lean_ctor_get(x_998, 1);
lean_inc(x_1035);
lean_dec(x_998);
x_1036 = lean_ctor_get(x_1006, 0);
lean_inc(x_1036);
lean_dec(x_1006);
x_1037 = lean_unsigned_to_nat(0u);
x_1038 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1037);
x_1039 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1038);
x_1040 = lean_mk_array(x_1038, x_1039);
x_1041 = lean_unsigned_to_nat(1u);
x_1042 = lean_nat_sub(x_1038, x_1041);
lean_dec(x_1038);
x_1043 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_1040, x_1042);
x_1044 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__3;
x_1045 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg(x_1036, x_996, x_1043, x_997, x_1044, x_2, x_3, x_4, x_5, x_1035);
lean_dec(x_1043);
lean_dec(x_996);
return x_1045;
}
default: 
{
lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; 
lean_dec(x_1006);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1046 = lean_ctor_get(x_998, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1047 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1047 = lean_box(0);
}
x_1048 = lean_expr_eqv(x_908, x_992);
lean_dec(x_908);
if (x_1048 == 0)
{
lean_object* x_1049; lean_object* x_1050; 
x_1049 = l_Lean_Expr_updateFn(x_1, x_992);
lean_dec(x_992);
if (lean_is_scalar(x_1047)) {
 x_1050 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1050 = x_1047;
}
lean_ctor_set(x_1050, 0, x_1049);
lean_ctor_set(x_1050, 1, x_1046);
return x_1050;
}
else
{
lean_object* x_1051; 
lean_dec(x_992);
if (lean_is_scalar(x_1047)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1047;
}
lean_ctor_set(x_1051, 0, x_1);
lean_ctor_set(x_1051, 1, x_1046);
return x_1051;
}
}
}
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_992);
lean_dec(x_908);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1052 = lean_ctor_get(x_998, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_998, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1054 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
uint8_t x_1056; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1056 = lean_expr_eqv(x_908, x_992);
lean_dec(x_908);
if (x_1056 == 0)
{
lean_object* x_1057; lean_object* x_1058; 
x_1057 = l_Lean_Expr_updateFn(x_1, x_992);
lean_dec(x_992);
x_1058 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1058, 0, x_1057);
lean_ctor_set(x_1058, 1, x_993);
return x_1058;
}
else
{
lean_object* x_1059; 
lean_dec(x_992);
x_1059 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1059, 0, x_1);
lean_ctor_set(x_1059, 1, x_993);
return x_1059;
}
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_908);
x_1060 = lean_unsigned_to_nat(0u);
x_1061 = l_Lean_Expr_getAppNumArgsAux(x_1, x_1060);
x_1062 = lean_mk_empty_array_with_capacity(x_1061);
lean_dec(x_1061);
x_1063 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_1062);
x_1064 = l_Lean_Expr_betaRev(x_992, x_1063);
lean_dec(x_1063);
lean_dec(x_992);
x_1 = x_1064;
x_6 = x_993;
goto _start;
}
}
}
else
{
uint8_t x_1066; 
lean_dec(x_908);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1066 = !lean_is_exclusive(x_909);
if (x_1066 == 0)
{
return x_909;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_909, 0);
x_1068 = lean_ctor_get(x_909, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_909);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
return x_1069;
}
}
}
case 8:
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1070 = lean_ctor_get(x_1, 2);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1, 3);
lean_inc(x_1071);
lean_dec(x_1);
x_1072 = lean_expr_instantiate1(x_1071, x_1070);
lean_dec(x_1070);
lean_dec(x_1071);
x_1 = x_1072;
x_6 = x_905;
goto _start;
}
case 11:
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1074 = lean_ctor_get(x_1, 1);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1, 2);
lean_inc(x_1075);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1076 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_1075, x_2, x_3, x_4, x_5, x_905);
if (lean_obj_tag(x_1076) == 0)
{
uint8_t x_1077; 
x_1077 = !lean_is_exclusive(x_1076);
if (x_1077 == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1076, 0);
x_1079 = lean_ctor_get(x_1076, 1);
x_1080 = l_Lean_Expr_getAppFn(x_1078);
if (lean_obj_tag(x_1080) == 4)
{
lean_object* x_1081; lean_object* x_1082; 
lean_free_object(x_1076);
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
lean_dec(x_1080);
x_1082 = l_Lean_Meta_getConst_x3f(x_1081, x_2, x_3, x_4, x_5, x_1079);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
if (lean_obj_tag(x_1083) == 0)
{
uint8_t x_1084; 
lean_dec(x_1078);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1084 = !lean_is_exclusive(x_1082);
if (x_1084 == 0)
{
lean_object* x_1085; 
x_1085 = lean_ctor_get(x_1082, 0);
lean_dec(x_1085);
lean_ctor_set(x_1082, 0, x_1);
return x_1082;
}
else
{
lean_object* x_1086; lean_object* x_1087; 
x_1086 = lean_ctor_get(x_1082, 1);
lean_inc(x_1086);
lean_dec(x_1082);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_1);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
else
{
lean_object* x_1088; 
x_1088 = lean_ctor_get(x_1083, 0);
lean_inc(x_1088);
lean_dec(x_1083);
if (lean_obj_tag(x_1088) == 6)
{
uint8_t x_1089; 
x_1089 = !lean_is_exclusive(x_1082);
if (x_1089 == 0)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; 
x_1090 = lean_ctor_get(x_1082, 1);
x_1091 = lean_ctor_get(x_1082, 0);
lean_dec(x_1091);
x_1092 = lean_ctor_get(x_1088, 0);
lean_inc(x_1092);
lean_dec(x_1088);
x_1093 = lean_ctor_get(x_1092, 3);
lean_inc(x_1093);
lean_dec(x_1092);
x_1094 = lean_nat_add(x_1093, x_1074);
lean_dec(x_1074);
lean_dec(x_1093);
x_1095 = lean_unsigned_to_nat(0u);
x_1096 = l_Lean_Expr_getAppNumArgsAux(x_1078, x_1095);
x_1097 = lean_nat_dec_lt(x_1094, x_1096);
if (x_1097 == 0)
{
lean_dec(x_1096);
lean_dec(x_1094);
lean_dec(x_1078);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_1082, 0, x_1);
return x_1082;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_free_object(x_1082);
lean_dec(x_1);
x_1098 = lean_nat_sub(x_1096, x_1094);
lean_dec(x_1094);
lean_dec(x_1096);
x_1099 = lean_unsigned_to_nat(1u);
x_1100 = lean_nat_sub(x_1098, x_1099);
lean_dec(x_1098);
x_1101 = l_Lean_Expr_getRevArg_x21(x_1078, x_1100);
lean_dec(x_1078);
x_1 = x_1101;
x_6 = x_1090;
goto _start;
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; 
x_1103 = lean_ctor_get(x_1082, 1);
lean_inc(x_1103);
lean_dec(x_1082);
x_1104 = lean_ctor_get(x_1088, 0);
lean_inc(x_1104);
lean_dec(x_1088);
x_1105 = lean_ctor_get(x_1104, 3);
lean_inc(x_1105);
lean_dec(x_1104);
x_1106 = lean_nat_add(x_1105, x_1074);
lean_dec(x_1074);
lean_dec(x_1105);
x_1107 = lean_unsigned_to_nat(0u);
x_1108 = l_Lean_Expr_getAppNumArgsAux(x_1078, x_1107);
x_1109 = lean_nat_dec_lt(x_1106, x_1108);
if (x_1109 == 0)
{
lean_object* x_1110; 
lean_dec(x_1108);
lean_dec(x_1106);
lean_dec(x_1078);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1);
lean_ctor_set(x_1110, 1, x_1103);
return x_1110;
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1);
x_1111 = lean_nat_sub(x_1108, x_1106);
lean_dec(x_1106);
lean_dec(x_1108);
x_1112 = lean_unsigned_to_nat(1u);
x_1113 = lean_nat_sub(x_1111, x_1112);
lean_dec(x_1111);
x_1114 = l_Lean_Expr_getRevArg_x21(x_1078, x_1113);
lean_dec(x_1078);
x_1 = x_1114;
x_6 = x_1103;
goto _start;
}
}
}
else
{
uint8_t x_1116; 
lean_dec(x_1088);
lean_dec(x_1078);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1116 = !lean_is_exclusive(x_1082);
if (x_1116 == 0)
{
lean_object* x_1117; 
x_1117 = lean_ctor_get(x_1082, 0);
lean_dec(x_1117);
lean_ctor_set(x_1082, 0, x_1);
return x_1082;
}
else
{
lean_object* x_1118; lean_object* x_1119; 
x_1118 = lean_ctor_get(x_1082, 1);
lean_inc(x_1118);
lean_dec(x_1082);
x_1119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1119, 0, x_1);
lean_ctor_set(x_1119, 1, x_1118);
return x_1119;
}
}
}
}
else
{
uint8_t x_1120; 
lean_dec(x_1078);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1120 = !lean_is_exclusive(x_1082);
if (x_1120 == 0)
{
return x_1082;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1082, 0);
x_1122 = lean_ctor_get(x_1082, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1082);
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set(x_1123, 1, x_1122);
return x_1123;
}
}
}
else
{
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_1076, 0, x_1);
return x_1076;
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1124 = lean_ctor_get(x_1076, 0);
x_1125 = lean_ctor_get(x_1076, 1);
lean_inc(x_1125);
lean_inc(x_1124);
lean_dec(x_1076);
x_1126 = l_Lean_Expr_getAppFn(x_1124);
if (lean_obj_tag(x_1126) == 4)
{
lean_object* x_1127; lean_object* x_1128; 
x_1127 = lean_ctor_get(x_1126, 0);
lean_inc(x_1127);
lean_dec(x_1126);
x_1128 = l_Lean_Meta_getConst_x3f(x_1127, x_2, x_3, x_4, x_5, x_1125);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; 
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1124);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1131 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1131 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1132 = x_1131;
}
lean_ctor_set(x_1132, 0, x_1);
lean_ctor_set(x_1132, 1, x_1130);
return x_1132;
}
else
{
lean_object* x_1133; 
x_1133 = lean_ctor_get(x_1129, 0);
lean_inc(x_1133);
lean_dec(x_1129);
if (lean_obj_tag(x_1133) == 6)
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; uint8_t x_1141; 
x_1134 = lean_ctor_get(x_1128, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1135 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1135 = lean_box(0);
}
x_1136 = lean_ctor_get(x_1133, 0);
lean_inc(x_1136);
lean_dec(x_1133);
x_1137 = lean_ctor_get(x_1136, 3);
lean_inc(x_1137);
lean_dec(x_1136);
x_1138 = lean_nat_add(x_1137, x_1074);
lean_dec(x_1074);
lean_dec(x_1137);
x_1139 = lean_unsigned_to_nat(0u);
x_1140 = l_Lean_Expr_getAppNumArgsAux(x_1124, x_1139);
x_1141 = lean_nat_dec_lt(x_1138, x_1140);
if (x_1141 == 0)
{
lean_object* x_1142; 
lean_dec(x_1140);
lean_dec(x_1138);
lean_dec(x_1124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_1135)) {
 x_1142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1142 = x_1135;
}
lean_ctor_set(x_1142, 0, x_1);
lean_ctor_set(x_1142, 1, x_1134);
return x_1142;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
lean_dec(x_1135);
lean_dec(x_1);
x_1143 = lean_nat_sub(x_1140, x_1138);
lean_dec(x_1138);
lean_dec(x_1140);
x_1144 = lean_unsigned_to_nat(1u);
x_1145 = lean_nat_sub(x_1143, x_1144);
lean_dec(x_1143);
x_1146 = l_Lean_Expr_getRevArg_x21(x_1124, x_1145);
lean_dec(x_1124);
x_1 = x_1146;
x_6 = x_1134;
goto _start;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1133);
lean_dec(x_1124);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1148 = lean_ctor_get(x_1128, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1149 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_1124);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1151 = lean_ctor_get(x_1128, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1128, 1);
lean_inc(x_1152);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1153 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1153 = lean_box(0);
}
if (lean_is_scalar(x_1153)) {
 x_1154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1154 = x_1153;
}
lean_ctor_set(x_1154, 0, x_1151);
lean_ctor_set(x_1154, 1, x_1152);
return x_1154;
}
}
else
{
lean_object* x_1155; 
lean_dec(x_1126);
lean_dec(x_1124);
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1155, 0, x_1);
lean_ctor_set(x_1155, 1, x_1125);
return x_1155;
}
}
}
else
{
uint8_t x_1156; 
lean_dec(x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1156 = !lean_is_exclusive(x_1076);
if (x_1156 == 0)
{
return x_1076;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_1076, 0);
x_1158 = lean_ctor_get(x_1076, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1076);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
default: 
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_1);
x_1160 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_1161 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__2;
x_1162 = lean_panic_fn(x_1160, x_1161);
x_1163 = lean_apply_5(x_1162, x_2, x_3, x_4, x_5, x_905);
return x_1163;
}
}
}
block_1171:
{
if (x_1165 == 0)
{
x_905 = x_1166;
goto block_1164;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
lean_inc(x_1);
x_1167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1167, 0, x_1);
x_1168 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
x_1169 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_1168, x_1167, x_2, x_3, x_4, x_5, x_1166);
x_1170 = lean_ctor_get(x_1169, 1);
lean_inc(x_1170);
lean_dec(x_1169);
x_905 = x_1170;
goto block_1164;
}
}
}
case 12:
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
lean_dec(x_1);
x_1184 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_1185 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_1186 = lean_panic_fn(x_1184, x_1185);
x_1187 = lean_apply_5(x_1186, x_2, x_3, x_4, x_5, x_6);
return x_1187;
}
default: 
{
lean_object* x_1188; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1188, 0, x_1);
lean_ctor_set(x_1188, 1, x_6);
return x_1188;
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
x_10 = l_List_lengthAux___main___rarg(x_8, x_9);
lean_dec(x_8);
x_11 = l_List_lengthAux___main___rarg(x_2, x_9);
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
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___main___rarg(x_2, x_10);
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
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___main___rarg(x_2, x_10);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_39 = x_30;
} else {
 lean_dec_ref(x_30);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_95 = l_Lean_ConstantInfo_lparams(x_40);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_List_lengthAux___main___rarg(x_95, x_96);
lean_dec(x_95);
x_98 = l_List_lengthAux___main___rarg(x_29, x_96);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = 1;
x_41 = x_100;
goto block_94;
}
else
{
uint8_t x_101; 
x_101 = 0;
x_41 = x_101;
goto block_94;
}
block_94:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
x_42 = l_Lean_ConstantInfo_name(x_40);
x_43 = l_Lean_Meta_smartUnfoldingSuffix;
x_44 = lean_name_mk_string(x_42, x_43);
x_45 = l_Lean_Meta_getConstNoEx_x3f(x_44, x_2, x_3, x_4, x_5, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = l_Lean_ConstantInfo_hasValue(x_40);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_45, 0, x_51);
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_45);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Expr_getAppNumArgsAux(x_1, x_52);
x_54 = lean_mk_empty_array_with_capacity(x_53);
lean_dec(x_53);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_54);
x_56 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_40, x_29, x_55, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_55);
lean_dec(x_29);
lean_dec(x_40);
return x_56;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_dec(x_45);
x_58 = l_Lean_ConstantInfo_hasValue(x_40);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_getAppNumArgsAux(x_1, x_61);
x_63 = lean_mk_empty_array_with_capacity(x_62);
lean_dec(x_62);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_63);
x_65 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_40, x_29, x_64, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_64);
lean_dec(x_29);
lean_dec(x_40);
return x_65;
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_46, 0);
lean_inc(x_66);
lean_dec(x_46);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_40);
x_67 = lean_ctor_get(x_45, 1);
lean_inc(x_67);
lean_dec(x_45);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Expr_getAppNumArgsAux(x_1, x_68);
x_70 = lean_mk_empty_array_with_capacity(x_69);
lean_dec(x_69);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_70);
x_72 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__3(x_66, x_29, x_71, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_71);
lean_dec(x_29);
lean_dec(x_66);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_66);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_45, 1);
x_75 = lean_ctor_get(x_45, 0);
lean_dec(x_75);
x_76 = l_Lean_ConstantInfo_hasValue(x_40);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_box(0);
lean_ctor_set(x_45, 0, x_77);
return x_45;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_45);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Expr_getAppNumArgsAux(x_1, x_78);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_80);
x_82 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_40, x_29, x_81, x_2, x_3, x_4, x_5, x_74);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_81);
lean_dec(x_29);
lean_dec(x_40);
return x_82;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
lean_dec(x_45);
x_84 = l_Lean_ConstantInfo_hasValue(x_40);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Expr_getAppNumArgsAux(x_1, x_87);
x_89 = lean_mk_empty_array_with_capacity(x_88);
lean_dec(x_88);
x_90 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_89);
x_91 = l___private_Lean_Meta_WHNF_0__Lean_Meta_deltaBetaDefinition___at___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f___spec__2(x_40, x_29, x_90, x_2, x_3, x_4, x_5, x_83);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_90);
lean_dec(x_29);
lean_dec(x_40);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_39;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_38);
return x_93;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_30);
if (x_102 == 0)
{
return x_30;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_30, 0);
x_104 = lean_ctor_get(x_30, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_30);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
return x_107;
}
}
default: 
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_6);
return x_109;
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
x_10 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_916____spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
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
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__4;
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
x_1 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_2 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_71 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_70, x_4, x_5, x_6, x_7, x_69);
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
x_49 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_47, x_48, x_4, x_5, x_6, x_7, x_41);
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
x_133 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_132, x_4, x_5, x_6, x_7, x_131);
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
x_108 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_111 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_110, x_109, x_4, x_5, x_6, x_7, x_98);
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
x_205 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_204, x_4, x_5, x_6, x_7, x_203);
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
x_188 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_186, x_187, x_4, x_5, x_6, x_7, x_180);
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
x_256 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_255, x_4, x_5, x_6, x_7, x_254);
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
x_236 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_239 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_238, x_237, x_4, x_5, x_6, x_7, x_226);
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
x_349 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_348, x_4, x_5, x_6, x_7, x_347);
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
x_319 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_327 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_326, x_325, x_4, x_5, x_6, x_7, x_311);
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
x_412 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_411, x_4, x_5, x_6, x_7, x_410);
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
x_383 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_392 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_391, x_390, x_4, x_5, x_6, x_7, x_376);
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
uint8_t x_7; uint8_t x_60; 
x_60 = l_Lean_Expr_hasFVar(x_1);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Expr_hasMVar(x_1);
x_7 = x_61;
goto block_59;
}
else
{
uint8_t x_62; 
x_62 = 1;
x_7 = x_62;
goto block_59;
}
block_59:
{
if (x_7 == 0)
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_toCtorIfLit___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Meta_reduceNat_x3f___closed__1;
x_16 = l_Lean_Meta_reduceUnaryNatOp(x_15, x_9, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
case 5:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_reduceNat_x3f___closed__3;
x_22 = lean_name_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_reduceNat_x3f___closed__5;
x_24 = lean_name_eq(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Meta_reduceNat_x3f___closed__7;
x_26 = lean_name_eq(x_20, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Meta_reduceNat_x3f___closed__9;
x_28 = lean_name_eq(x_20, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_reduceNat_x3f___closed__11;
x_30 = lean_name_eq(x_20, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_reduceNat_x3f___closed__13;
x_32 = lean_name_eq(x_20, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_reduceNat_x3f___closed__15;
x_34 = lean_name_eq(x_20, x_33);
lean_dec(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Meta_reduceNat_x3f___closed__16;
x_38 = l_Lean_Meta_reduceBinNatPred(x_37, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
x_39 = l_Lean_Meta_reduceNat_x3f___closed__17;
x_40 = l_Lean_Meta_reduceBinNatPred(x_39, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_41 = l_Nat_HasMod___closed__1;
x_42 = l_Lean_Meta_reduceBinNatOp(x_41, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_20);
x_43 = l_Nat_HasDiv___closed__1;
x_44 = l_Lean_Meta_reduceBinNatOp(x_43, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_20);
x_45 = l_Nat_HasMul___closed__1;
x_46 = l_Lean_Meta_reduceBinNatOp(x_45, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_20);
x_47 = l_Nat_HasSub___closed__1;
x_48 = l_Lean_Meta_reduceBinNatOp(x_47, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_20);
x_49 = l_Nat_HasAdd___closed__1;
x_50 = l_Lean_Meta_reduceBinNatOp(x_49, x_19, x_18, x_2, x_3, x_4, x_5, x_6);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
}
default: 
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_6);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_6);
return x_58;
}
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
x_3 = lean_unsigned_to_nat(413u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
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
x_3 = lean_unsigned_to_nat(423u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_14, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 4);
lean_inc(x_43);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_44 = x_14;
} else {
 lean_dec_ref(x_14);
 x_44 = lean_box(0);
}
lean_inc(x_3);
x_45 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_43, x_2, x_3);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_38);
x_48 = lean_st_ref_set(x_5, x_47, x_15);
lean_dec(x_5);
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
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_52 = lean_st_ref_take(x_5, x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_53, 1);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_54, 3);
lean_inc(x_3);
x_60 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_59, x_2, x_3);
lean_ctor_set(x_54, 3, x_60);
x_61 = lean_st_ref_set(x_5, x_53, x_55);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_3);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_54, 0);
x_67 = lean_ctor_get(x_54, 1);
x_68 = lean_ctor_get(x_54, 2);
x_69 = lean_ctor_get(x_54, 4);
x_70 = lean_ctor_get(x_54, 3);
lean_inc(x_69);
lean_inc(x_70);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
lean_inc(x_3);
x_71 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_70, x_2, x_3);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_69);
lean_ctor_set(x_53, 1, x_72);
x_73 = lean_st_ref_set(x_5, x_53, x_55);
lean_dec(x_5);
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
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_3);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_53, 0);
x_78 = lean_ctor_get(x_53, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_53);
x_79 = lean_ctor_get(x_54, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_54, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_54, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_54, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_54, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 x_84 = x_54;
} else {
 lean_dec_ref(x_54);
 x_84 = lean_box(0);
}
lean_inc(x_3);
x_85 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_83, x_2, x_3);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set(x_86, 4, x_82);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_78);
x_88 = lean_st_ref_set(x_5, x_87, x_55);
lean_dec(x_5);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_3);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
x_92 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_93 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___closed__2;
x_94 = lean_panic_fn(x_92, x_93);
x_95 = lean_apply_5(x_94, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_3);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
if (x_20 == 0)
{
uint8_t x_49; 
x_49 = 0;
x_25 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_22, 6);
if (x_50 == 0)
{
x_25 = x_20;
goto block_48;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_25 = x_51;
goto block_48;
}
}
block_48:
{
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_24);
lean_dec(x_1);
x_26 = lean_ctor_get_uint8(x_22, 7);
lean_dec(x_22);
if (x_26 == 0)
{
lean_dec(x_11);
x_1 = x_19;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_3, x_23);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_11, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_st_ref_set(x_3, x_43, x_30);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_1 = x_19;
x_6 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_24)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_24;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_23);
return x_47;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_56, x_2, x_3, x_4, x_5, x_6);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
lean_ctor_set(x_57, 0, x_1);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_1 = x_64;
x_6 = x_63;
goto _start;
}
}
case 4:
{
uint8_t x_66; lean_object* x_67; uint8_t x_137; 
x_137 = l_Lean_Expr_hasFVar(x_1);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = l_Lean_Expr_hasExprMVar(x_1);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_2, 0);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_139, 5);
lean_dec(x_139);
x_141 = 2;
x_142 = l_Lean_Meta_TransparencyMode_beq(x_140, x_141);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = 1;
x_66 = x_143;
x_67 = x_6;
goto block_136;
}
else
{
uint8_t x_144; 
x_144 = 0;
x_66 = x_144;
x_67 = x_6;
goto block_136;
}
}
else
{
uint8_t x_145; 
x_145 = 0;
x_66 = x_145;
x_67 = x_6;
goto block_136;
}
}
else
{
uint8_t x_146; 
x_146 = 0;
x_66 = x_146;
x_67 = x_6;
goto block_136;
}
block_136:
{
lean_object* x_68; lean_object* x_69; 
if (x_66 == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_68 = x_111;
x_69 = x_67;
goto block_110;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_st_ref_get(x_3, x_67);
x_113 = lean_ctor_get(x_2, 0);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_113, 5);
lean_dec(x_113);
switch (x_114) {
case 0:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_117, 4);
lean_inc(x_118);
lean_dec(x_117);
x_119 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_118, x_1);
x_68 = x_119;
x_69 = x_116;
goto block_110;
}
case 1:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_112, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
lean_dec(x_112);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_122, 3);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_123, x_1);
x_68 = x_124;
x_69 = x_121;
goto block_110;
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
lean_dec(x_112);
x_126 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_127 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_128 = lean_panic_fn(x_126, x_127);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_129 = lean_apply_5(x_128, x_2, x_3, x_4, x_5, x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_68 = x_130;
x_69 = x_131;
goto block_110;
}
else
{
uint8_t x_132; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_129, 0);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_129);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
block_110:
{
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_70; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_71);
x_73 = l_Lean_Meta_reduceNat_x3f(x_71, x_2, x_3, x_4, x_5, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_71);
x_76 = l_Lean_Meta_reduceNative_x3f(x_71, x_2, x_3, x_4, x_5, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_71);
x_79 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_71, x_2, x_3, x_4, x_5, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_66, x_1, x_71, x_2, x_3, x_4, x_5, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
lean_dec(x_1);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_1 = x_84;
x_6 = x_83;
goto _start;
}
}
else
{
uint8_t x_86; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_79, 0);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_71);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_dec(x_76);
x_91 = lean_ctor_get(x_77, 0);
lean_inc(x_91);
lean_dec(x_77);
x_92 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_66, x_1, x_91, x_2, x_3, x_4, x_5, x_90);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_76);
if (x_93 == 0)
{
return x_76;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_76, 0);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_76);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_71);
x_97 = lean_ctor_get(x_73, 1);
lean_inc(x_97);
lean_dec(x_73);
x_98 = lean_ctor_get(x_74, 0);
lean_inc(x_98);
lean_dec(x_74);
x_99 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_66, x_1, x_98, x_2, x_3, x_4, x_5, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_73);
if (x_100 == 0)
{
return x_73;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_73, 0);
x_102 = lean_ctor_get(x_73, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_73);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_68, 0);
lean_inc(x_108);
lean_dec(x_68);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_69);
return x_109;
}
}
}
}
case 5:
{
uint8_t x_147; lean_object* x_148; uint8_t x_218; 
x_218 = l_Lean_Expr_hasFVar(x_1);
if (x_218 == 0)
{
uint8_t x_219; 
x_219 = l_Lean_Expr_hasExprMVar(x_1);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_2, 0);
lean_inc(x_220);
x_221 = lean_ctor_get_uint8(x_220, 5);
lean_dec(x_220);
x_222 = 2;
x_223 = l_Lean_Meta_TransparencyMode_beq(x_221, x_222);
if (x_223 == 0)
{
uint8_t x_224; 
x_224 = 1;
x_147 = x_224;
x_148 = x_6;
goto block_217;
}
else
{
uint8_t x_225; 
x_225 = 0;
x_147 = x_225;
x_148 = x_6;
goto block_217;
}
}
else
{
uint8_t x_226; 
x_226 = 0;
x_147 = x_226;
x_148 = x_6;
goto block_217;
}
}
else
{
uint8_t x_227; 
x_227 = 0;
x_147 = x_227;
x_148 = x_6;
goto block_217;
}
block_217:
{
lean_object* x_149; lean_object* x_150; 
if (x_147 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_149 = x_192;
x_150 = x_148;
goto block_191;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_st_ref_get(x_3, x_148);
x_194 = lean_ctor_get(x_2, 0);
lean_inc(x_194);
x_195 = lean_ctor_get_uint8(x_194, 5);
lean_dec(x_194);
switch (x_195) {
case 0:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
lean_dec(x_193);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_198, 4);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_199, x_1);
x_149 = x_200;
x_150 = x_197;
goto block_191;
}
case 1:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
lean_dec(x_193);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_203, 3);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_204, x_1);
x_149 = x_205;
x_150 = x_202;
goto block_191;
}
default: 
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_193, 1);
lean_inc(x_206);
lean_dec(x_193);
x_207 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_208 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_209 = lean_panic_fn(x_207, x_208);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_210 = lean_apply_5(x_209, x_2, x_3, x_4, x_5, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_149 = x_211;
x_150 = x_212;
goto block_191;
}
else
{
uint8_t x_213; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_210);
if (x_213 == 0)
{
return x_210;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_210, 0);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_210);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
}
block_191:
{
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_151; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_151 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_152);
x_154 = l_Lean_Meta_reduceNat_x3f(x_152, x_2, x_3, x_4, x_5, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_152);
x_157 = l_Lean_Meta_reduceNative_x3f(x_152, x_2, x_3, x_4, x_5, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_152);
x_160 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_152, x_2, x_3, x_4, x_5, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_147, x_1, x_152, x_2, x_3, x_4, x_5, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_152);
lean_dec(x_1);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
lean_dec(x_161);
x_1 = x_165;
x_6 = x_164;
goto _start;
}
}
else
{
uint8_t x_167; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_160);
if (x_167 == 0)
{
return x_160;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_160, 0);
x_169 = lean_ctor_get(x_160, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_160);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_152);
x_171 = lean_ctor_get(x_157, 1);
lean_inc(x_171);
lean_dec(x_157);
x_172 = lean_ctor_get(x_158, 0);
lean_inc(x_172);
lean_dec(x_158);
x_173 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_147, x_1, x_172, x_2, x_3, x_4, x_5, x_171);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_157);
if (x_174 == 0)
{
return x_157;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_157, 0);
x_176 = lean_ctor_get(x_157, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_157);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_152);
x_178 = lean_ctor_get(x_154, 1);
lean_inc(x_178);
lean_dec(x_154);
x_179 = lean_ctor_get(x_155, 0);
lean_inc(x_179);
lean_dec(x_155);
x_180 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_147, x_1, x_179, x_2, x_3, x_4, x_5, x_178);
return x_180;
}
}
else
{
uint8_t x_181; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_154);
if (x_181 == 0)
{
return x_154;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_154, 0);
x_183 = lean_ctor_get(x_154, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_154);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_151);
if (x_185 == 0)
{
return x_151;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_151, 0);
x_187 = lean_ctor_get(x_151, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_151);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_149, 0);
lean_inc(x_189);
lean_dec(x_149);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_150);
return x_190;
}
}
}
}
case 8:
{
uint8_t x_228; lean_object* x_229; uint8_t x_299; 
x_299 = l_Lean_Expr_hasFVar(x_1);
if (x_299 == 0)
{
uint8_t x_300; 
x_300 = l_Lean_Expr_hasExprMVar(x_1);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_2, 0);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_301, 5);
lean_dec(x_301);
x_303 = 2;
x_304 = l_Lean_Meta_TransparencyMode_beq(x_302, x_303);
if (x_304 == 0)
{
uint8_t x_305; 
x_305 = 1;
x_228 = x_305;
x_229 = x_6;
goto block_298;
}
else
{
uint8_t x_306; 
x_306 = 0;
x_228 = x_306;
x_229 = x_6;
goto block_298;
}
}
else
{
uint8_t x_307; 
x_307 = 0;
x_228 = x_307;
x_229 = x_6;
goto block_298;
}
}
else
{
uint8_t x_308; 
x_308 = 0;
x_228 = x_308;
x_229 = x_6;
goto block_298;
}
block_298:
{
lean_object* x_230; lean_object* x_231; 
if (x_228 == 0)
{
lean_object* x_273; 
x_273 = lean_box(0);
x_230 = x_273;
x_231 = x_229;
goto block_272;
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_274 = lean_st_ref_get(x_3, x_229);
x_275 = lean_ctor_get(x_2, 0);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_275, 5);
lean_dec(x_275);
switch (x_276) {
case 0:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_279, 4);
lean_inc(x_280);
lean_dec(x_279);
x_281 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_280, x_1);
x_230 = x_281;
x_231 = x_278;
goto block_272;
}
case 1:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_274, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_274, 1);
lean_inc(x_283);
lean_dec(x_274);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get(x_284, 3);
lean_inc(x_285);
lean_dec(x_284);
x_286 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_285, x_1);
x_230 = x_286;
x_231 = x_283;
goto block_272;
}
default: 
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_274, 1);
lean_inc(x_287);
lean_dec(x_274);
x_288 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_289 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_290 = lean_panic_fn(x_288, x_289);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_291 = lean_apply_5(x_290, x_2, x_3, x_4, x_5, x_287);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_230 = x_292;
x_231 = x_293;
goto block_272;
}
else
{
uint8_t x_294; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_291);
if (x_294 == 0)
{
return x_291;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_291, 0);
x_296 = lean_ctor_get(x_291, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_291);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
}
block_272:
{
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_232; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_232 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_233);
x_235 = l_Lean_Meta_reduceNat_x3f(x_233, x_2, x_3, x_4, x_5, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_233);
x_238 = l_Lean_Meta_reduceNative_x3f(x_233, x_2, x_3, x_4, x_5, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_233);
x_241 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_233, x_2, x_3, x_4, x_5, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_228, x_1, x_233, x_2, x_3, x_4, x_5, x_243);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_233);
lean_dec(x_1);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_dec(x_241);
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
lean_dec(x_242);
x_1 = x_246;
x_6 = x_245;
goto _start;
}
}
else
{
uint8_t x_248; 
lean_dec(x_233);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = !lean_is_exclusive(x_241);
if (x_248 == 0)
{
return x_241;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_241, 0);
x_250 = lean_ctor_get(x_241, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_241);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_233);
x_252 = lean_ctor_get(x_238, 1);
lean_inc(x_252);
lean_dec(x_238);
x_253 = lean_ctor_get(x_239, 0);
lean_inc(x_253);
lean_dec(x_239);
x_254 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_228, x_1, x_253, x_2, x_3, x_4, x_5, x_252);
return x_254;
}
}
else
{
uint8_t x_255; 
lean_dec(x_233);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_238);
if (x_255 == 0)
{
return x_238;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_238, 0);
x_257 = lean_ctor_get(x_238, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_238);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_233);
x_259 = lean_ctor_get(x_235, 1);
lean_inc(x_259);
lean_dec(x_235);
x_260 = lean_ctor_get(x_236, 0);
lean_inc(x_260);
lean_dec(x_236);
x_261 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_228, x_1, x_260, x_2, x_3, x_4, x_5, x_259);
return x_261;
}
}
else
{
uint8_t x_262; 
lean_dec(x_233);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_235);
if (x_262 == 0)
{
return x_235;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_235, 0);
x_264 = lean_ctor_get(x_235, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_235);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_232);
if (x_266 == 0)
{
return x_232;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_232, 0);
x_268 = lean_ctor_get(x_232, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_232);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_230, 0);
lean_inc(x_270);
lean_dec(x_230);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_231);
return x_271;
}
}
}
}
case 10:
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_1, 1);
lean_inc(x_309);
lean_dec(x_1);
x_1 = x_309;
goto _start;
}
case 11:
{
uint8_t x_311; lean_object* x_312; uint8_t x_382; 
x_382 = l_Lean_Expr_hasFVar(x_1);
if (x_382 == 0)
{
uint8_t x_383; 
x_383 = l_Lean_Expr_hasExprMVar(x_1);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; uint8_t x_386; uint8_t x_387; 
x_384 = lean_ctor_get(x_2, 0);
lean_inc(x_384);
x_385 = lean_ctor_get_uint8(x_384, 5);
lean_dec(x_384);
x_386 = 2;
x_387 = l_Lean_Meta_TransparencyMode_beq(x_385, x_386);
if (x_387 == 0)
{
uint8_t x_388; 
x_388 = 1;
x_311 = x_388;
x_312 = x_6;
goto block_381;
}
else
{
uint8_t x_389; 
x_389 = 0;
x_311 = x_389;
x_312 = x_6;
goto block_381;
}
}
else
{
uint8_t x_390; 
x_390 = 0;
x_311 = x_390;
x_312 = x_6;
goto block_381;
}
}
else
{
uint8_t x_391; 
x_391 = 0;
x_311 = x_391;
x_312 = x_6;
goto block_381;
}
block_381:
{
lean_object* x_313; lean_object* x_314; 
if (x_311 == 0)
{
lean_object* x_356; 
x_356 = lean_box(0);
x_313 = x_356;
x_314 = x_312;
goto block_355;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_357 = lean_st_ref_get(x_3, x_312);
x_358 = lean_ctor_get(x_2, 0);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_358, 5);
lean_dec(x_358);
switch (x_359) {
case 0:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_360 = lean_ctor_get(x_357, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_362, 4);
lean_inc(x_363);
lean_dec(x_362);
x_364 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_363, x_1);
x_313 = x_364;
x_314 = x_361;
goto block_355;
}
case 1:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_365 = lean_ctor_get(x_357, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_357, 1);
lean_inc(x_366);
lean_dec(x_357);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_ctor_get(x_367, 3);
lean_inc(x_368);
lean_dec(x_367);
x_369 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_368, x_1);
x_313 = x_369;
x_314 = x_366;
goto block_355;
}
default: 
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_370 = lean_ctor_get(x_357, 1);
lean_inc(x_370);
lean_dec(x_357);
x_371 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_372 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___closed__2;
x_373 = lean_panic_fn(x_371, x_372);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_374 = lean_apply_5(x_373, x_2, x_3, x_4, x_5, x_370);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_313 = x_375;
x_314 = x_376;
goto block_355;
}
else
{
uint8_t x_377; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_374);
if (x_377 == 0)
{
return x_374;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_374, 0);
x_379 = lean_ctor_get(x_374, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_374);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
}
}
block_355:
{
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_315; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_315 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_316);
x_318 = l_Lean_Meta_reduceNat_x3f(x_316, x_2, x_3, x_4, x_5, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
lean_inc(x_316);
x_321 = l_Lean_Meta_reduceNative_x3f(x_316, x_2, x_3, x_4, x_5, x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_316);
x_324 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_316, x_2, x_3, x_4, x_5, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_311, x_1, x_316, x_2, x_3, x_4, x_5, x_326);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_316);
lean_dec(x_1);
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_ctor_get(x_325, 0);
lean_inc(x_329);
lean_dec(x_325);
x_1 = x_329;
x_6 = x_328;
goto _start;
}
}
else
{
uint8_t x_331; 
lean_dec(x_316);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_324);
if (x_331 == 0)
{
return x_324;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_324, 0);
x_333 = lean_ctor_get(x_324, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_324);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_316);
x_335 = lean_ctor_get(x_321, 1);
lean_inc(x_335);
lean_dec(x_321);
x_336 = lean_ctor_get(x_322, 0);
lean_inc(x_336);
lean_dec(x_322);
x_337 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_311, x_1, x_336, x_2, x_3, x_4, x_5, x_335);
return x_337;
}
}
else
{
uint8_t x_338; 
lean_dec(x_316);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_338 = !lean_is_exclusive(x_321);
if (x_338 == 0)
{
return x_321;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_321, 0);
x_340 = lean_ctor_get(x_321, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_321);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_316);
x_342 = lean_ctor_get(x_318, 1);
lean_inc(x_342);
lean_dec(x_318);
x_343 = lean_ctor_get(x_319, 0);
lean_inc(x_343);
lean_dec(x_319);
x_344 = l___private_Lean_Meta_WHNF_0__Lean_Meta_cache(x_311, x_1, x_343, x_2, x_3, x_4, x_5, x_342);
return x_344;
}
}
else
{
uint8_t x_345; 
lean_dec(x_316);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_318);
if (x_345 == 0)
{
return x_318;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_318, 0);
x_347 = lean_ctor_get(x_318, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_318);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_315);
if (x_349 == 0)
{
return x_315;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_315, 0);
x_351 = lean_ctor_get(x_315, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_315);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = lean_ctor_get(x_313, 0);
lean_inc(x_353);
lean_dec(x_313);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_314);
return x_354;
}
}
}
}
case 12:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_1);
x_392 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_393 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_394 = lean_panic_fn(x_392, x_393);
x_395 = lean_apply_5(x_394, x_2, x_3, x_4, x_5, x_6);
return x_395;
}
default: 
{
lean_object* x_396; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_1);
lean_ctor_set(x_396, 1, x_6);
return x_396;
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
if (x_21 == 0)
{
uint8_t x_50; 
x_50 = 0;
x_26 = x_50;
goto block_49;
}
else
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_23, 6);
if (x_51 == 0)
{
x_26 = x_21;
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = 0;
x_26 = x_52;
goto block_49;
}
}
block_49:
{
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_25);
lean_dec(x_2);
x_27 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_12);
x_2 = x_20;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_st_ref_take(x_4, x_24);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
x_41 = lean_ctor_get(x_30, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_42 = lean_box(0);
x_43 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_41, x_12, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_31);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_2 = x_20;
x_7 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_25)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_25;
}
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_24);
return x_48;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 2:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_57, x_3, x_4, x_5, x_6, x_7);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_2 = x_65;
x_7 = x_64;
goto _start;
}
}
case 4:
{
lean_object* x_67; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_67 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = l_Lean_Expr_isAppOf(x_69, x_1);
if (x_71 == 0)
{
lean_object* x_72; 
lean_free_object(x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_72 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_69, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
lean_ctor_set(x_72, 0, x_69);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
x_2 = x_79;
x_7 = x_78;
goto _start;
}
}
else
{
uint8_t x_81; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_72);
if (x_81 == 0)
{
return x_72;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_72, 0);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_72);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_67, 0);
x_86 = lean_ctor_get(x_67, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_67);
x_87 = l_Lean_Expr_isAppOf(x_85, x_1);
if (x_87 == 0)
{
lean_object* x_88; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_85);
x_88 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_85, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_85);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec(x_89);
x_2 = x_94;
x_7 = x_93;
goto _start;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_85);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_98 = x_88;
} else {
 lean_dec_ref(x_88);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_85);
lean_ctor_set(x_100, 1, x_86);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_67);
if (x_101 == 0)
{
return x_67;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_67, 0);
x_103 = lean_ctor_get(x_67, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_67);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 5:
{
lean_object* x_105; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Expr_isAppOf(x_107, x_1);
if (x_109 == 0)
{
lean_object* x_110; 
lean_free_object(x_105);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_107);
x_110 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_107, x_3, x_4, x_5, x_6, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 0, x_107);
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_107);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
lean_dec(x_111);
x_2 = x_117;
x_7 = x_116;
goto _start;
}
}
else
{
uint8_t x_119; 
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_110);
if (x_119 == 0)
{
return x_110;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_110, 0);
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_110);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_105;
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_105, 0);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_105);
x_125 = l_Lean_Expr_isAppOf(x_123, x_1);
if (x_125 == 0)
{
lean_object* x_126; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_123);
x_126 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_123, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_123);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
x_2 = x_132;
x_7 = x_131;
goto _start;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_136 = x_126;
} else {
 lean_dec_ref(x_126);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_123);
lean_ctor_set(x_138, 1, x_124);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_105);
if (x_139 == 0)
{
return x_105;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_105, 0);
x_141 = lean_ctor_get(x_105, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_105);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 8:
{
lean_object* x_143; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
x_147 = l_Lean_Expr_isAppOf(x_145, x_1);
if (x_147 == 0)
{
lean_object* x_148; 
lean_free_object(x_143);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_145);
x_148 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_145, x_3, x_4, x_5, x_6, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_148, 0);
lean_dec(x_151);
lean_ctor_set(x_148, 0, x_145);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_145);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
lean_dec(x_149);
x_2 = x_155;
x_7 = x_154;
goto _start;
}
}
else
{
uint8_t x_157; 
lean_dec(x_145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_148);
if (x_157 == 0)
{
return x_148;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_148, 0);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_148);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_143;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_143, 0);
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_143);
x_163 = l_Lean_Expr_isAppOf(x_161, x_1);
if (x_163 == 0)
{
lean_object* x_164; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_161);
x_164 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_161, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_161);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
lean_dec(x_165);
x_2 = x_170;
x_7 = x_169;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = lean_ctor_get(x_164, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_164, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_174 = x_164;
} else {
 lean_dec_ref(x_164);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_161);
lean_ctor_set(x_176, 1, x_162);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_143);
if (x_177 == 0)
{
return x_143;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_143, 0);
x_179 = lean_ctor_get(x_143, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_143);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
case 10:
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
lean_dec(x_2);
x_2 = x_181;
goto _start;
}
case 11:
{
lean_object* x_183; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_183 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_ctor_get(x_183, 1);
x_187 = l_Lean_Expr_isAppOf(x_185, x_1);
if (x_187 == 0)
{
lean_object* x_188; 
lean_free_object(x_183);
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
uint8_t x_190; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = !lean_is_exclusive(x_188);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_188, 0);
lean_dec(x_191);
lean_ctor_set(x_188, 0, x_185);
return x_188;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_185);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_185);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_dec(x_188);
x_195 = lean_ctor_get(x_189, 0);
lean_inc(x_195);
lean_dec(x_189);
x_2 = x_195;
x_7 = x_194;
goto _start;
}
}
else
{
uint8_t x_197; 
lean_dec(x_185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = !lean_is_exclusive(x_188);
if (x_197 == 0)
{
return x_188;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_188, 0);
x_199 = lean_ctor_get(x_188, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_188);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_183;
}
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_183, 0);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_183);
x_203 = l_Lean_Expr_isAppOf(x_201, x_1);
if (x_203 == 0)
{
lean_object* x_204; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_201);
x_204 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_201, x_3, x_4, x_5, x_6, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_201);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_201);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_dec(x_204);
x_210 = lean_ctor_get(x_205, 0);
lean_inc(x_210);
lean_dec(x_205);
x_2 = x_210;
x_7 = x_209;
goto _start;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_212 = lean_ctor_get(x_204, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_204, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_214 = x_204;
} else {
 lean_dec_ref(x_204);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_201);
lean_ctor_set(x_216, 1, x_202);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = !lean_is_exclusive(x_183);
if (x_217 == 0)
{
return x_183;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_183, 0);
x_219 = lean_ctor_get(x_183, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_183);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
case 12:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_2);
x_221 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_222 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_223 = lean_panic_fn(x_221, x_222);
x_224 = lean_apply_5(x_223, x_3, x_4, x_5, x_6, x_7);
return x_224;
}
default: 
{
lean_object* x_225; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_2);
lean_ctor_set(x_225, 1, x_7);
return x_225;
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
uint8_t x_8; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_1);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
lean_object* l_Lean_Meta_whnfUntil___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_whnfUntil___spec__1___boxed), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4520_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2___closed__5;
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
l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1 = _init_l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1);
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_4520_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
