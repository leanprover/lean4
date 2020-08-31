// Lean compiler output
// Module: Lean.Meta.WHNF
// Imports: Init Lean.AuxRecursor Lean.Util.WHNF Lean.Meta.Basic Lean.Meta.LevelDefEq
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
lean_object* l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__1;
lean_object* l_Lean_Meta_getConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l___private_Lean_Meta_WHNF_6__cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__7;
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__3;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__16;
lean_object* l_Lean_Meta_reduceNative_x3f___closed__6;
lean_object* l___private_Lean_Meta_WHNF_4__useWHNFCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue(lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Meta_unfoldDefinition_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__5;
extern lean_object* l_Nat_HasMod___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_HasMul___closed__1;
lean_object* l_Lean_Meta_reduceBinNatPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_WHNF_5__isIdRhsApp(lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_5__cached_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__5;
lean_object* l_Lean_Meta_setWHNFRef___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_getConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_3__getRecRuleFor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___rarg(lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__6;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_getStuckMVar_x3f___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_toCtorIfLit(lean_object*);
lean_object* l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__12;
lean_object* l_Lean_Meta_reduceBoolNative___rarg(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef(lean_object*);
extern lean_object* l_Lean_Exception_inhabited___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__10;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__10;
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
extern lean_object* l_Nat_HasAdd___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__11;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_6__extractIdRhs(lean_object*);
extern lean_object* l_Lean_WHNF_toCtorIfLit___closed__2;
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_reduceUnaryNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__1;
lean_object* l_Lean_Meta_whnfHeadPredAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__3;
lean_object* l_Lean_Meta_reduceBinNatOp___closed__7;
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_WHNF_toCtorIfLit___closed__4;
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l___private_Lean_Meta_WHNF_3__whnfCoreImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNativeConst(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_5__cached_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__9;
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_WHNF_smartUnfoldingSuffix;
lean_object* l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__4;
lean_object* l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__8;
lean_object* l_Lean_Meta_reduceNativeConst___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_1__getFirstCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__17;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__6;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_HasDiv___closed__1;
lean_object* l___private_Lean_Meta_WHNF_4__useWHNFCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__11;
lean_object* l_Lean_Meta_whnfHeadPred(lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_9__whnfCoreUnstuck___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_getStuckMVar_x3f___main___at_Lean_Meta_getStuckMVar_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
extern lean_object* l_Nat_HasSub___closed__1;
lean_object* l_Lean_Meta_reduceNatNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStuckMVar_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__13;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__12;
lean_object* l_Lean_Meta_whnfImpl___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_whnfUntil___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_6__cache(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__4;
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__8;
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
lean_object* l_Lean_Meta_whnfCore(lean_object*);
lean_object* l_Lean_Meta_whnfUntil___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__2;
lean_object* l_Lean_Meta_reduceNativeConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__15;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__2;
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__14;
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__1;
lean_object* l_Lean_Meta_whnfImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBoolNative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Meta_reduceNat_x3f___closed__5;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNatNativeUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__4;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__3;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceBinNatOp___closed__9;
lean_object* l_Lean_Meta_whnfUntil(lean_object*);
lean_object* l_Lean_Meta_reduceNat_x3f___closed__6;
lean_object* l_Lean_Meta_whnfHeadPred___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__2;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f___boxed), 6, 1);
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
lean_object* l_Lean_Meta_isAuxDef_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_18 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_18 = l_Lean_Expr_updateFn___main(x_1, x_3);
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
x_23 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_22);
x_24 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_23, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_111; lean_object* x_112; 
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_112 = lean_box(x_111);
switch (lean_obj_tag(x_112)) {
case 2:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_unsigned_to_nat(5u);
x_114 = lean_unsigned_to_nat(3u);
x_12 = x_113;
x_13 = x_114;
goto block_110;
}
case 3:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_unsigned_to_nat(3u);
x_12 = x_115;
x_13 = x_116;
goto block_110;
}
default: 
{
uint8_t x_117; 
lean_dec(x_112);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_117 = lean_expr_eqv(x_2, x_3);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_11);
return x_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_11);
return x_120;
}
}
}
block_110:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_expr_eqv(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_6, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_getConstNoEx_x3f(x_28, x_7, x_8, x_9, x_10, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_2, x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_expr_eqv(x_2, x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
x_43 = lean_box(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l_Lean_Expr_Inhabited;
x_46 = lean_array_get(x_45, x_6, x_13);
x_47 = l_Lean_mkApp(x_46, x_27);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_12, x_48);
x_50 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_14, x_6, x_49, x_47);
lean_dec(x_14);
x_51 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_50, x_7, x_8, x_9, x_10, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_29, 0);
lean_dec(x_53);
x_54 = lean_expr_eqv(x_2, x_3);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_55);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_expr_eqv(x_2, x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_29);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_29, 0);
lean_dec(x_62);
x_63 = lean_expr_eqv(x_2, x_3);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_64);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_expr_eqv(x_2, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_21, 0);
lean_dec(x_71);
x_72 = lean_expr_eqv(x_2, x_3);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_73);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_expr_eqv(x_2, x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_21);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_21, 0);
lean_dec(x_80);
x_81 = lean_expr_eqv(x_2, x_3);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_82);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_21, 1);
lean_inc(x_83);
lean_dec(x_21);
x_84 = lean_expr_eqv(x_2, x_3);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_21, 0);
lean_dec(x_89);
x_90 = lean_expr_eqv(x_2, x_3);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_91);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_21, 1);
lean_inc(x_92);
lean_dec(x_21);
x_93 = lean_expr_eqv(x_2, x_3);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_21);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_21, 0);
lean_dec(x_98);
x_99 = lean_expr_eqv(x_2, x_3);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_100);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_21, 1);
lean_inc(x_101);
lean_dec(x_21);
x_102 = lean_expr_eqv(x_2, x_3);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_101);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_21);
if (x_106 == 0)
{
return x_21;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_21, 0);
x_108 = lean_ctor_get(x_21, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_21);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_WHNF_1__getFirstCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
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
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
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
uint8_t x_20; 
lean_free_object(x_9);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_9);
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_8, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_8, 0, x_34);
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
lean_dec(x_9);
if (lean_obj_tag(x_38) == 5)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 4);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_42 = x_8;
} else {
 lean_dec_ref(x_8);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_46 = x_8;
} else {
 lean_dec_ref(x_8);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_51 = x_8;
} else {
 lean_dec_ref(x_8);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Util_WHNF_1__getFirstCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__12(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
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
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = l_Lean_mkConst(x_23, x_11);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_25);
x_27 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_28, x_30);
x_32 = l_Array_shrink___main___rarg(x_31, x_3);
x_33 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_32, x_32, x_25, x_24);
lean_dec(x_32);
lean_ctor_set(x_13, 0, x_33);
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
x_35 = l_Lean_mkConst(x_34, x_11);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_39, x_41);
x_43 = l_Array_shrink___main___rarg(x_42, x_3);
x_44 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_43, x_43, x_36, x_35);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_12, 0, x_45);
return x_12;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_48 = x_13;
} else {
 lean_dec_ref(x_13);
 x_48 = lean_box(0);
}
x_49 = l_Lean_mkConst(x_47, x_11);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_50);
x_52 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_51);
x_53 = lean_mk_array(x_51, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_51, x_54);
lean_dec(x_51);
x_56 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_53, x_55);
x_57 = l_Array_shrink___main___rarg(x_56, x_3);
x_58 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_57, x_57, x_50, x_49);
lean_dec(x_57);
if (lean_is_scalar(x_48)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_48;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConstNoEx_x3f___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn___main(x_13);
x_16 = l_Lean_RecursorVal_getInduct(x_1);
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasExprMVar(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_11);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_22 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_21, x_13, x_20, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_31 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_30, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_32, x_3, x_4, x_5, x_6, x_33);
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
lean_free_object(x_23);
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
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_23);
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
lean_free_object(x_23);
lean_dec(x_30);
lean_dec(x_13);
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
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_56 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_55, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_57, x_3, x_4, x_5, x_6, x_58);
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
lean_dec(x_13);
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
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_22);
if (x_78 == 0)
{
return x_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_22, 0);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_22);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_82);
x_84 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
lean_inc(x_13);
x_88 = l___private_Lean_Expr_3__getAppArgsAux___main(x_13, x_85, x_87);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_array_get_size(x_88);
x_91 = lean_nat_dec_le(x_90, x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_inc(x_89);
x_92 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13(x_13, x_88, x_90, x_89);
lean_dec(x_90);
lean_dec(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_free_object(x_11);
x_93 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_94 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_93, x_13, x_89, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = !lean_is_exclusive(x_95);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_103 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_102, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_104, x_3, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_free_object(x_95);
lean_dec(x_102);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set(x_106, 0, x_111);
return x_106;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_106, 0);
lean_dec(x_116);
lean_ctor_set(x_106, 0, x_95);
return x_106;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_106, 1);
lean_inc(x_117);
lean_dec(x_106);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_95);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_95);
lean_dec(x_102);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
return x_106;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_106, 0);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_106);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_95);
lean_dec(x_102);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_103);
if (x_123 == 0)
{
return x_103;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_103, 0);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_103);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_95, 0);
lean_inc(x_127);
lean_dec(x_95);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_127);
x_128 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_127, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_129, x_3, x_4, x_5, x_6, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_127);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_127);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_127);
x_142 = lean_ctor_get(x_131, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_144 = x_131;
} else {
 lean_dec_ref(x_131);
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
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_128, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_148 = x_128;
} else {
 lean_dec_ref(x_128);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_94);
if (x_150 == 0)
{
return x_94;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_94, 0);
x_152 = lean_ctor_get(x_94, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_94);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_box(0);
lean_ctor_set(x_11, 0, x_154);
return x_11;
}
}
else
{
uint8_t x_155; 
lean_inc(x_89);
x_155 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14(x_13, lean_box(0), x_88, x_90, x_89);
lean_dec(x_90);
lean_dec(x_88);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_free_object(x_11);
x_156 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_157 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_156, x_13, x_89, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = !lean_is_exclusive(x_158);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_158, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_165);
x_166 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_165, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_167, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
lean_free_object(x_158);
lean_dec(x_165);
x_172 = !lean_is_exclusive(x_169);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_169, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set(x_169, 0, x_174);
return x_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_169);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_169, 0);
lean_dec(x_179);
lean_ctor_set(x_169, 0, x_158);
return x_169;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_dec(x_169);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_158);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_free_object(x_158);
lean_dec(x_165);
x_182 = !lean_is_exclusive(x_169);
if (x_182 == 0)
{
return x_169;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_169, 0);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_169);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_free_object(x_158);
lean_dec(x_165);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = !lean_is_exclusive(x_166);
if (x_186 == 0)
{
return x_166;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_166, 0);
x_188 = lean_ctor_get(x_166, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_166);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_158, 0);
lean_inc(x_190);
lean_dec(x_158);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_190);
x_191 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_190, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_13, x_192, x_3, x_4, x_5, x_6, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_190);
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
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_194, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_202 = x_194;
} else {
 lean_dec_ref(x_194);
 x_202 = lean_box(0);
}
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_190);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_190);
x_205 = lean_ctor_get(x_194, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_194, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_207 = x_194;
} else {
 lean_dec_ref(x_194);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_190);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = lean_ctor_get(x_191, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_191, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_211 = x_191;
} else {
 lean_dec_ref(x_191);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_157);
if (x_213 == 0)
{
return x_157;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_157, 0);
x_215 = lean_ctor_get(x_157, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_157);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_box(0);
lean_ctor_set(x_11, 0, x_217);
return x_11;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_218 = lean_ctor_get(x_11, 0);
x_219 = lean_ctor_get(x_11, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_11);
x_220 = l_Lean_Expr_getAppFn___main(x_218);
x_221 = l_Lean_RecursorVal_getInduct(x_1);
x_222 = l_Lean_Expr_isConstOf(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_219);
return x_224;
}
else
{
uint8_t x_225; 
x_225 = l_Lean_Expr_hasExprMVar(x_218);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_1, 2);
lean_inc(x_226);
lean_dec(x_1);
x_227 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_228 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_227, x_218, x_226, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_218);
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
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_235 = x_229;
} else {
 lean_dec_ref(x_229);
 x_235 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_234);
x_236 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_234, x_3, x_4, x_5, x_6, x_233);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_218, x_237, x_3, x_4, x_5, x_6, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_235);
lean_dec(x_234);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_243 = x_239;
} else {
 lean_dec_ref(x_239);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_239, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_247 = x_239;
} else {
 lean_dec_ref(x_239);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_235;
}
lean_ctor_set(x_248, 0, x_234);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_235);
lean_dec(x_234);
x_250 = lean_ctor_get(x_239, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_239, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_252 = x_239;
} else {
 lean_dec_ref(x_239);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = lean_ctor_get(x_236, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_236, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_256 = x_236;
} else {
 lean_dec_ref(x_236);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_ctor_get(x_228, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_228, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_260 = x_228;
} else {
 lean_dec_ref(x_228);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_262 = lean_unsigned_to_nat(0u);
x_263 = l_Lean_Expr_getAppNumArgsAux___main(x_218, x_262);
x_264 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_263);
x_265 = lean_mk_array(x_263, x_264);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_sub(x_263, x_266);
lean_dec(x_263);
lean_inc(x_218);
x_268 = l___private_Lean_Expr_3__getAppArgsAux___main(x_218, x_265, x_267);
x_269 = lean_ctor_get(x_1, 2);
lean_inc(x_269);
lean_dec(x_1);
x_270 = lean_array_get_size(x_268);
x_271 = lean_nat_dec_le(x_270, x_270);
if (x_271 == 0)
{
uint8_t x_272; 
lean_inc(x_269);
x_272 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13(x_218, x_268, x_270, x_269);
lean_dec(x_270);
lean_dec(x_268);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_274 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_273, x_218, x_269, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_269);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
lean_dec(x_274);
x_280 = lean_ctor_get(x_275, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
 x_281 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_280);
x_282 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_280, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_218, x_283, x_3, x_4, x_5, x_6, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_281);
lean_dec(x_280);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
x_290 = lean_box(0);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_288);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_293 = x_285;
} else {
 lean_dec_ref(x_285);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_281;
}
lean_ctor_set(x_294, 0, x_280);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_281);
lean_dec(x_280);
x_296 = lean_ctor_get(x_285, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_298 = x_285;
} else {
 lean_dec_ref(x_285);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_300 = lean_ctor_get(x_282, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_282, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_302 = x_282;
} else {
 lean_dec_ref(x_282);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_304 = lean_ctor_get(x_274, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_274, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_306 = x_274;
} else {
 lean_dec_ref(x_274);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_269);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_219);
return x_309;
}
}
else
{
uint8_t x_310; 
lean_inc(x_269);
x_310 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14(x_218, lean_box(0), x_268, x_270, x_269);
lean_dec(x_270);
lean_dec(x_268);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_312 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_311, x_218, x_269, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_269);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
lean_dec(x_312);
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_319 = x_313;
} else {
 lean_dec_ref(x_313);
 x_319 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_318);
x_320 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_318, x_3, x_4, x_5, x_6, x_317);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_218, x_321, x_3, x_4, x_5, x_6, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_unbox(x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_319);
lean_dec(x_318);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_327 = x_323;
} else {
 lean_dec_ref(x_323);
 x_327 = lean_box(0);
}
x_328 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_326);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_323, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_331 = x_323;
} else {
 lean_dec_ref(x_323);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_319;
}
lean_ctor_set(x_332, 0, x_318);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_330);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_319);
lean_dec(x_318);
x_334 = lean_ctor_get(x_323, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_323, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_336 = x_323;
} else {
 lean_dec_ref(x_323);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = lean_ctor_get(x_320, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_320, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_340 = x_320;
} else {
 lean_dec_ref(x_320);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_342 = lean_ctor_get(x_312, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_312, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_344 = x_312;
} else {
 lean_dec_ref(x_312);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_269);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_219);
return x_347;
}
}
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_11);
if (x_348 == 0)
{
return x_11;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_11, 0);
x_350 = lean_ctor_get(x_11, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_11);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
else
{
uint8_t x_352; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_352 = !lean_is_exclusive(x_8);
if (x_352 == 0)
{
return x_8;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_8, 0);
x_354 = lean_ctor_get(x_8, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_8);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
}
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_RecursorVal_getMajorIdx(x_4);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_15 = lean_expr_eqv(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_6, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_65; 
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
x_65 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_66 = l_Lean_WHNF_toCtorIfLit(x_21);
lean_inc(x_4);
x_67 = l___private_Lean_Util_WHNF_3__getRecRuleFor(x_4, x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_68 = lean_expr_eqv(x_2, x_3);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_22);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_22);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Expr_getAppNumArgsAux___main(x_66, x_73);
x_75 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_74);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = l___private_Lean_Expr_3__getAppArgsAux___main(x_66, x_76, x_78);
x_80 = l_List_lengthAux___main___rarg(x_5, x_73);
x_81 = lean_ctor_get(x_4, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_List_lengthAux___main___rarg(x_82, x_73);
x_84 = lean_nat_dec_eq(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_85 = lean_expr_eqv(x_2, x_3);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_22);
return x_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_22);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 2);
lean_inc(x_89);
x_90 = l_Lean_Expr_instantiateLevelParams(x_89, x_82, x_5);
lean_dec(x_82);
x_91 = lean_ctor_get(x_4, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_4, 4);
lean_inc(x_92);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
x_94 = lean_ctor_get(x_4, 5);
lean_inc(x_94);
lean_dec(x_4);
x_95 = lean_nat_add(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
x_96 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_95, x_6, x_73, x_90);
lean_dec(x_95);
x_97 = lean_array_get_size(x_79);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
lean_dec(x_72);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_97, x_79, x_99, x_96);
lean_dec(x_79);
lean_dec(x_97);
x_101 = lean_nat_add(x_12, x_77);
lean_dec(x_12);
x_102 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_13, x_6, x_101, x_100);
lean_dec(x_13);
x_103 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_102, x_7, x_8, x_9, x_10, x_22);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
lean_inc(x_4);
x_104 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10(x_4, x_21, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_24 = x_21;
x_25 = x_106;
goto block_64;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_21);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
x_24 = x_108;
x_25 = x_107;
goto block_64;
}
}
else
{
uint8_t x_109; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_WHNF_toCtorIfLit(x_24);
lean_inc(x_4);
x_27 = l___private_Lean_Util_WHNF_3__getRecRuleFor(x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_28 = lean_expr_eqv(x_2, x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_33);
x_35 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Lean_Expr_3__getAppArgsAux___main(x_26, x_36, x_38);
x_40 = l_List_lengthAux___main___rarg(x_5, x_33);
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_lengthAux___main___rarg(x_42, x_33);
x_44 = lean_nat_dec_eq(x_40, x_43);
lean_dec(x_43);
lean_dec(x_40);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_45 = lean_expr_eqv(x_2, x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_23)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_23;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_25);
return x_47;
}
else
{
lean_object* x_48; 
if (lean_is_scalar(x_23)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_23;
}
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_25);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
lean_dec(x_1);
x_49 = lean_ctor_get(x_32, 2);
lean_inc(x_49);
x_50 = l_Lean_Expr_instantiateLevelParams(x_49, x_42, x_5);
lean_dec(x_42);
x_51 = lean_ctor_get(x_4, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 4);
lean_inc(x_52);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_4, 5);
lean_inc(x_54);
lean_dec(x_4);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_55, x_6, x_33, x_50);
lean_dec(x_55);
x_57 = lean_array_get_size(x_39);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_57, x_39, x_59, x_56);
lean_dec(x_39);
lean_dec(x_57);
x_61 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
x_62 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_13, x_6, x_61, x_60);
lean_dec(x_13);
x_63 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_62, x_7, x_8, x_9, x_10, x_25);
return x_63;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_20);
if (x_113 == 0)
{
return x_20;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_20, 0);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_20);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalDecl_value_x3f(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_7(x_11, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_7(x_10, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_13 = l_Lean_Expr_Inhabited;
x_14 = l_monadInhabited___rarg(x_1, x_13);
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_apply_5(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1___boxed), 8, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
x_21 = lean_apply_9(x_18, lean_box(0), lean_box(0), x_19, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1___boxed), 6, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__2), 8, 2);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
x_26 = lean_apply_9(x_23, lean_box(0), lean_box(0), x_24, x_25, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
case 4:
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = l_Lean_Expr_getAppFn___main(x_28);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_30 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Lean_Expr_isLambda(x_32);
if (x_34 == 0)
{
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_30);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = l_Lean_Meta_getConstNoEx_x3f(x_35, x_3, x_4, x_5, x_6, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
switch (lean_obj_tag(x_48)) {
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
x_50 = l_Lean_ConstantInfo_name(x_48);
x_51 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_50, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_51, 0, x_2);
return x_51;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_32);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_64);
x_66 = lean_mk_empty_array_with_capacity(x_65);
lean_dec(x_65);
lean_inc(x_2);
x_67 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_66);
x_68 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7(x_2, x_29, x_32, x_48, x_36, x_67, x_3, x_4, x_5, x_6, x_63);
lean_dec(x_67);
lean_dec(x_36);
lean_dec(x_48);
lean_dec(x_32);
lean_dec(x_29);
return x_68;
}
}
case 4:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
lean_dec(x_48);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_71);
x_73 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_72);
x_74 = lean_mk_array(x_72, x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_72, x_75);
lean_dec(x_72);
lean_inc(x_2);
x_77 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_74, x_76);
x_78 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8(x_2, x_29, x_32, x_70, x_36, x_77, x_3, x_4, x_5, x_6, x_69);
lean_dec(x_77);
lean_dec(x_36);
lean_dec(x_70);
lean_dec(x_32);
lean_dec(x_29);
return x_78;
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_37, 1);
lean_inc(x_79);
lean_dec(x_37);
x_80 = lean_ctor_get(x_48, 0);
lean_inc(x_80);
lean_dec(x_48);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_81);
x_83 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_82);
x_84 = lean_mk_array(x_82, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_82, x_85);
lean_dec(x_82);
lean_inc(x_2);
x_87 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_84, x_86);
x_88 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9(x_2, x_29, x_32, x_80, x_36, x_87, x_3, x_4, x_5, x_6, x_79);
lean_dec(x_87);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_29);
return x_88;
}
default: 
{
uint8_t x_89; 
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_37);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_37, 0);
lean_dec(x_90);
x_91 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_92);
return x_37;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
lean_dec(x_37);
x_94 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_32);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_99);
return x_30;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_30);
lean_dec(x_29);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_100);
x_102 = lean_mk_empty_array_with_capacity(x_101);
lean_dec(x_101);
x_103 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_102);
x_104 = l_Lean_Expr_betaRev(x_32, x_103);
lean_dec(x_103);
lean_dec(x_32);
x_105 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_104, x_3, x_4, x_5, x_6, x_33);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_30, 0);
x_107 = lean_ctor_get(x_30, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_30);
x_108 = l_Lean_Expr_isLambda(x_106);
if (x_108 == 0)
{
if (lean_obj_tag(x_106) == 4)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
x_111 = l_Lean_Meta_getConstNoEx_x3f(x_109, x_3, x_4, x_5, x_6, x_107);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_106);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_2);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
switch (lean_obj_tag(x_119)) {
case 1:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_dec(x_111);
x_121 = l_Lean_ConstantInfo_name(x_119);
x_122 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_121, x_3, x_4, x_5, x_6, x_120);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_119);
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_126;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
return x_129;
}
else
{
lean_object* x_130; 
lean_dec(x_106);
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_125);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_dec(x_122);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_132);
x_134 = lean_mk_empty_array_with_capacity(x_133);
lean_dec(x_133);
lean_inc(x_2);
x_135 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_134);
x_136 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7(x_2, x_29, x_106, x_119, x_110, x_135, x_3, x_4, x_5, x_6, x_131);
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_119);
lean_dec(x_106);
lean_dec(x_29);
return x_136;
}
}
case 4:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_111, 1);
lean_inc(x_137);
lean_dec(x_111);
x_138 = lean_ctor_get(x_119, 0);
lean_inc(x_138);
lean_dec(x_119);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_139);
x_141 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_140, x_143);
lean_dec(x_140);
lean_inc(x_2);
x_145 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_142, x_144);
x_146 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8(x_2, x_29, x_106, x_138, x_110, x_145, x_3, x_4, x_5, x_6, x_137);
lean_dec(x_145);
lean_dec(x_110);
lean_dec(x_138);
lean_dec(x_106);
lean_dec(x_29);
return x_146;
}
case 7:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_111, 1);
lean_inc(x_147);
lean_dec(x_111);
x_148 = lean_ctor_get(x_119, 0);
lean_inc(x_148);
lean_dec(x_119);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_149);
x_151 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_150);
x_152 = lean_mk_array(x_150, x_151);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_sub(x_150, x_153);
lean_dec(x_150);
lean_inc(x_2);
x_155 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_152, x_154);
x_156 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9(x_2, x_29, x_106, x_148, x_110, x_155, x_3, x_4, x_5, x_6, x_147);
lean_dec(x_155);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_29);
return x_156;
}
default: 
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_111, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_158 = x_111;
} else {
 lean_dec_ref(x_111);
 x_158 = lean_box(0);
}
x_159 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
return x_161;
}
else
{
lean_object* x_162; 
lean_dec(x_106);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_2);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
}
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
x_163 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_107);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_106);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_2);
lean_ctor_set(x_166, 1, x_107);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_29);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_167);
x_169 = lean_mk_empty_array_with_capacity(x_168);
lean_dec(x_168);
x_170 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_169);
x_171 = l_Lean_Expr_betaRev(x_106, x_170);
lean_dec(x_170);
lean_dec(x_106);
x_172 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_171, x_3, x_4, x_5, x_6, x_107);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_30);
if (x_173 == 0)
{
return x_30;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_30, 0);
x_175 = lean_ctor_get(x_30, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_30);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
case 8:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_1);
x_177 = lean_ctor_get(x_2, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_2, 3);
lean_inc(x_178);
lean_dec(x_2);
x_179 = lean_expr_instantiate1(x_178, x_177);
lean_dec(x_177);
lean_dec(x_178);
x_180 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_179, x_3, x_4, x_5, x_6, x_7);
return x_180;
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
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_1);
x_183 = lean_ctor_get(x_2, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_185 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_184, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = l_Lean_Expr_getAppFn___main(x_187);
if (lean_obj_tag(x_189) == 4)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_free_object(x_185);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_Meta_getConstNoEx_x3f(x_190, x_3, x_4, x_5, x_6, x_188);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
lean_dec(x_187);
lean_dec(x_183);
x_193 = !lean_is_exclusive(x_191);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 0);
lean_dec(x_194);
lean_ctor_set(x_191, 0, x_2);
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
lean_dec(x_192);
if (lean_obj_tag(x_197) == 6)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_191);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_191, 0);
lean_dec(x_199);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
lean_dec(x_197);
x_201 = lean_ctor_get(x_200, 3);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_nat_add(x_201, x_183);
lean_dec(x_183);
lean_dec(x_201);
x_203 = lean_unsigned_to_nat(0u);
x_204 = l_Lean_Expr_getAppNumArgsAux___main(x_187, x_203);
x_205 = lean_nat_sub(x_204, x_202);
lean_dec(x_202);
lean_dec(x_204);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_sub(x_205, x_206);
lean_dec(x_205);
x_208 = l_Lean_Expr_getRevArgD___main(x_187, x_207, x_2);
lean_dec(x_2);
lean_dec(x_187);
lean_ctor_set(x_191, 0, x_208);
return x_191;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_ctor_get(x_191, 1);
lean_inc(x_209);
lean_dec(x_191);
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
lean_dec(x_197);
x_211 = lean_ctor_get(x_210, 3);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_nat_add(x_211, x_183);
lean_dec(x_183);
lean_dec(x_211);
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Lean_Expr_getAppNumArgsAux___main(x_187, x_213);
x_215 = lean_nat_sub(x_214, x_212);
lean_dec(x_212);
lean_dec(x_214);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_nat_sub(x_215, x_216);
lean_dec(x_215);
x_218 = l_Lean_Expr_getRevArgD___main(x_187, x_217, x_2);
lean_dec(x_2);
lean_dec(x_187);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_209);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_183);
x_220 = !lean_is_exclusive(x_191);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_191, 0);
lean_dec(x_221);
lean_ctor_set(x_191, 0, x_2);
return x_191;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_191, 1);
lean_inc(x_222);
lean_dec(x_191);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_2);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
else
{
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_185, 0, x_2);
return x_185;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_185, 0);
x_225 = lean_ctor_get(x_185, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_185);
x_226 = l_Lean_Expr_getAppFn___main(x_224);
if (lean_obj_tag(x_226) == 4)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_Lean_Meta_getConstNoEx_x3f(x_227, x_3, x_4, x_5, x_6, x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_224);
lean_dec(x_183);
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
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
lean_dec(x_229);
if (lean_obj_tag(x_233) == 6)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_235 = x_228;
} else {
 lean_dec_ref(x_228);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_236, 3);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_nat_add(x_237, x_183);
lean_dec(x_183);
lean_dec(x_237);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Lean_Expr_getAppNumArgsAux___main(x_224, x_239);
x_241 = lean_nat_sub(x_240, x_238);
lean_dec(x_238);
lean_dec(x_240);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_sub(x_241, x_242);
lean_dec(x_241);
x_244 = l_Lean_Expr_getRevArgD___main(x_224, x_243, x_2);
lean_dec(x_2);
lean_dec(x_224);
if (lean_is_scalar(x_235)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_235;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_234);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_233);
lean_dec(x_224);
lean_dec(x_183);
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_247 = x_228;
} else {
 lean_dec_ref(x_228);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_2);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_225);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_185);
if (x_250 == 0)
{
return x_185;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_185, 0);
x_252 = lean_ctor_get(x_185, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_185);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
case 12:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_2);
x_254 = l_Lean_Expr_Inhabited;
x_255 = l_monadInhabited___rarg(x_1, x_254);
x_256 = l_unreachable_x21___rarg(x_255);
x_257 = lean_apply_5(x_256, x_3, x_4, x_5, x_6, x_7);
return x_257;
}
default: 
{
lean_object* x_258; 
x_258 = lean_box(0);
x_8 = x_258;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_7(x_10, lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
lean_object* l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_8 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_24; lean_object* x_25; 
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_25 = lean_box(x_24);
switch (lean_obj_tag(x_25)) {
case 2:
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(5u);
x_9 = x_26;
goto block_23;
}
case 3:
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(4u);
x_9 = x_27;
goto block_23;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
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
}
block_23:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_WHNF_getStuckMVar_x3f___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__16(x_16, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
lean_object* l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_WHNF_getStuckMVar_x3f___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__16(x_17, x_4, x_5, x_6, x_7, x_18);
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
lean_object* l_Lean_WHNF_getStuckMVar_x3f___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Expr_getAppFn___main(x_10);
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
x_29 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_31, x_33);
x_35 = l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17(x_27, x_16, x_34, x_2, x_3, x_4, x_5, x_26);
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
x_39 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_38);
x_40 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_41, x_43);
x_45 = l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18(x_37, x_16, x_44, x_2, x_3, x_4, x_5, x_36);
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
x_57 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_56, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l___private_Lean_Util_WHNF_9__whnfCoreUnstuck___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l_Lean_WHNF_getStuckMVar_x3f___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__16(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_18 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_17);
x_19 = l___private_Lean_Util_WHNF_9__whnfCoreUnstuck___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__5(x_18, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l___private_Lean_Util_WHNF_5__isIdRhsApp(x_21);
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
x_24 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_21);
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
x_28 = l___private_Lean_Util_WHNF_5__isIdRhsApp(x_26);
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
x_31 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_26);
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
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3(x_17, x_8, x_2, x_3, x_4, x_5, x_18);
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
x_27 = l_Lean_Expr_getAppFn___main(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
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
x_44 = l_List_lengthAux___main___rarg(x_42, x_43);
lean_dec(x_42);
x_45 = l_List_lengthAux___main___rarg(x_29, x_43);
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
x_49 = l_Lean_WHNF_smartUnfoldingSuffix;
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
x_58 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_43);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_59);
x_61 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_41, x_29, x_60, x_2, x_3, x_4, x_5, x_54);
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
x_66 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_43);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
x_68 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_67);
x_69 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_41, x_29, x_68, x_2, x_3, x_4, x_5, x_62);
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
x_72 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_43);
x_73 = lean_mk_empty_array_with_capacity(x_72);
lean_dec(x_72);
x_74 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_73);
x_75 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19(x_70, x_29, x_74, x_2, x_3, x_4, x_5, x_71);
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
x_81 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_43);
x_82 = lean_mk_empty_array_with_capacity(x_81);
lean_dec(x_81);
x_83 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_82);
x_84 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_41, x_29, x_83, x_2, x_3, x_4, x_5, x_77);
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
x_89 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_43);
x_90 = lean_mk_empty_array_with_capacity(x_89);
lean_dec(x_89);
x_91 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_90);
x_92 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_41, x_29, x_91, x_2, x_3, x_4, x_5, x_85);
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
x_97 = l_List_lengthAux___main___rarg(x_95, x_96);
lean_dec(x_95);
x_98 = l_List_lengthAux___main___rarg(x_29, x_96);
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
x_103 = l_Lean_WHNF_smartUnfoldingSuffix;
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
x_112 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_96);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
x_114 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_113);
x_115 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_94, x_29, x_114, x_2, x_3, x_4, x_5, x_107);
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
x_118 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_96);
x_119 = lean_mk_empty_array_with_capacity(x_118);
lean_dec(x_118);
x_120 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_119);
x_121 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19(x_116, x_29, x_120, x_2, x_3, x_4, x_5, x_117);
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
x_127 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_96);
x_128 = lean_mk_empty_array_with_capacity(x_127);
lean_dec(x_127);
x_129 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_128);
x_130 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_94, x_29, x_129, x_2, x_3, x_4, x_5, x_122);
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
lean_object* x_131; lean_object* x_132; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_6);
return x_132;
}
}
default: 
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_6);
return x_134;
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_isAuxDef_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isAuxDef_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_WHNF_7__deltaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__14(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__15___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_isQuotRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_isRecStuck_x3f___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f), 6, 1);
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
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_18 = l_Lean_Expr_updateFn___main(x_1, x_3);
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
x_23 = l___private_Lean_Util_WHNF_6__extractIdRhs(x_22);
x_24 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_23, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_111; lean_object* x_112; 
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_112 = lean_box(x_111);
switch (lean_obj_tag(x_112)) {
case 2:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_unsigned_to_nat(5u);
x_114 = lean_unsigned_to_nat(3u);
x_12 = x_113;
x_13 = x_114;
goto block_110;
}
case 3:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_unsigned_to_nat(3u);
x_12 = x_115;
x_13 = x_116;
goto block_110;
}
default: 
{
uint8_t x_117; 
lean_dec(x_112);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_117 = lean_expr_eqv(x_2, x_3);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_11);
return x_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_11);
return x_120;
}
}
}
block_110:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_expr_eqv(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_6, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_getConstNoEx_x3f(x_28, x_7, x_8, x_9, x_10, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_2, x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_expr_eqv(x_2, x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
x_43 = lean_box(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l_Lean_Expr_Inhabited;
x_46 = lean_array_get(x_45, x_6, x_13);
x_47 = l_Lean_mkApp(x_46, x_27);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_12, x_48);
x_50 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_14, x_6, x_49, x_47);
lean_dec(x_14);
x_51 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_50, x_7, x_8, x_9, x_10, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_29, 0);
lean_dec(x_53);
x_54 = lean_expr_eqv(x_2, x_3);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_55);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_expr_eqv(x_2, x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_29);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_29, 0);
lean_dec(x_62);
x_63 = lean_expr_eqv(x_2, x_3);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_64);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_expr_eqv(x_2, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_21, 0);
lean_dec(x_71);
x_72 = lean_expr_eqv(x_2, x_3);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_73);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_expr_eqv(x_2, x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_21);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_21, 0);
lean_dec(x_80);
x_81 = lean_expr_eqv(x_2, x_3);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_82);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_21, 1);
lean_inc(x_83);
lean_dec(x_21);
x_84 = lean_expr_eqv(x_2, x_3);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_21, 0);
lean_dec(x_89);
x_90 = lean_expr_eqv(x_2, x_3);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_91);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_21, 1);
lean_inc(x_92);
lean_dec(x_21);
x_93 = lean_expr_eqv(x_2, x_3);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_21);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_21, 0);
lean_dec(x_98);
x_99 = lean_expr_eqv(x_2, x_3);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_21, 0, x_100);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_21, 1);
lean_inc(x_101);
lean_dec(x_21);
x_102 = lean_expr_eqv(x_2, x_3);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_101);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_21);
if (x_106 == 0)
{
return x_21;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_21, 0);
x_108 = lean_ctor_get(x_21, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_21);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn___main(x_13);
x_16 = l_Lean_RecursorVal_getInduct(x_1);
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasExprMVar(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_11);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_22 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_21, x_13, x_20, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_31 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_30, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_isExprDefEqAux(x_13, x_32, x_3, x_4, x_5, x_6, x_33);
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
lean_free_object(x_23);
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
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_23);
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
lean_free_object(x_23);
lean_dec(x_30);
lean_dec(x_13);
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
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_56 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_55, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_isExprDefEqAux(x_13, x_57, x_3, x_4, x_5, x_6, x_58);
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
lean_dec(x_13);
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
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_22);
if (x_78 == 0)
{
return x_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_22, 0);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_22);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_82);
x_84 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
lean_inc(x_13);
x_88 = l___private_Lean_Expr_3__getAppArgsAux___main(x_13, x_85, x_87);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_array_get_size(x_88);
x_91 = lean_nat_dec_le(x_90, x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_inc(x_89);
x_92 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6(x_13, x_88, x_90, x_89);
lean_dec(x_90);
lean_dec(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_free_object(x_11);
x_93 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_94 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_93, x_13, x_89, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = !lean_is_exclusive(x_95);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_103 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_102, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_isExprDefEqAux(x_13, x_104, x_3, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_free_object(x_95);
lean_dec(x_102);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set(x_106, 0, x_111);
return x_106;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_106, 0);
lean_dec(x_116);
lean_ctor_set(x_106, 0, x_95);
return x_106;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_106, 1);
lean_inc(x_117);
lean_dec(x_106);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_95);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_95);
lean_dec(x_102);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
return x_106;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_106, 0);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_106);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_95);
lean_dec(x_102);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_103);
if (x_123 == 0)
{
return x_103;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_103, 0);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_103);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_95, 0);
lean_inc(x_127);
lean_dec(x_95);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_127);
x_128 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_127, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_isExprDefEqAux(x_13, x_129, x_3, x_4, x_5, x_6, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_127);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_127);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_127);
x_142 = lean_ctor_get(x_131, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_144 = x_131;
} else {
 lean_dec_ref(x_131);
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
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_128, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_148 = x_128;
} else {
 lean_dec_ref(x_128);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_94);
if (x_150 == 0)
{
return x_94;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_94, 0);
x_152 = lean_ctor_get(x_94, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_94);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_box(0);
lean_ctor_set(x_11, 0, x_154);
return x_11;
}
}
else
{
uint8_t x_155; 
lean_inc(x_89);
x_155 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7(x_13, lean_box(0), x_88, x_90, x_89);
lean_dec(x_90);
lean_dec(x_88);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_free_object(x_11);
x_156 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_157 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_156, x_13, x_89, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = !lean_is_exclusive(x_158);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_158, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_165);
x_166 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_165, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Meta_isExprDefEqAux(x_13, x_167, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
lean_free_object(x_158);
lean_dec(x_165);
x_172 = !lean_is_exclusive(x_169);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_169, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set(x_169, 0, x_174);
return x_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_169);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_169, 0);
lean_dec(x_179);
lean_ctor_set(x_169, 0, x_158);
return x_169;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_dec(x_169);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_158);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_free_object(x_158);
lean_dec(x_165);
x_182 = !lean_is_exclusive(x_169);
if (x_182 == 0)
{
return x_169;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_169, 0);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_169);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_free_object(x_158);
lean_dec(x_165);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = !lean_is_exclusive(x_166);
if (x_186 == 0)
{
return x_166;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_166, 0);
x_188 = lean_ctor_get(x_166, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_166);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_158, 0);
lean_inc(x_190);
lean_dec(x_158);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_190);
x_191 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_190, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_isExprDefEqAux(x_13, x_192, x_3, x_4, x_5, x_6, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_190);
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
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_194, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_202 = x_194;
} else {
 lean_dec_ref(x_194);
 x_202 = lean_box(0);
}
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_190);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_190);
x_205 = lean_ctor_get(x_194, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_194, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_207 = x_194;
} else {
 lean_dec_ref(x_194);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_190);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = lean_ctor_get(x_191, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_191, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_211 = x_191;
} else {
 lean_dec_ref(x_191);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_157);
if (x_213 == 0)
{
return x_157;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_157, 0);
x_215 = lean_ctor_get(x_157, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_157);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_box(0);
lean_ctor_set(x_11, 0, x_217);
return x_11;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_218 = lean_ctor_get(x_11, 0);
x_219 = lean_ctor_get(x_11, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_11);
x_220 = l_Lean_Expr_getAppFn___main(x_218);
x_221 = l_Lean_RecursorVal_getInduct(x_1);
x_222 = l_Lean_Expr_isConstOf(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_219);
return x_224;
}
else
{
uint8_t x_225; 
x_225 = l_Lean_Expr_hasExprMVar(x_218);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_1, 2);
lean_inc(x_226);
lean_dec(x_1);
x_227 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_228 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_227, x_218, x_226, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_218);
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
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_235 = x_229;
} else {
 lean_dec_ref(x_229);
 x_235 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_234);
x_236 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_234, x_3, x_4, x_5, x_6, x_233);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Meta_isExprDefEqAux(x_218, x_237, x_3, x_4, x_5, x_6, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_235);
lean_dec(x_234);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_243 = x_239;
} else {
 lean_dec_ref(x_239);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_239, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_247 = x_239;
} else {
 lean_dec_ref(x_239);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_235;
}
lean_ctor_set(x_248, 0, x_234);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_235);
lean_dec(x_234);
x_250 = lean_ctor_get(x_239, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_239, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_252 = x_239;
} else {
 lean_dec_ref(x_239);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = lean_ctor_get(x_236, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_236, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_256 = x_236;
} else {
 lean_dec_ref(x_236);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_ctor_get(x_228, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_228, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_260 = x_228;
} else {
 lean_dec_ref(x_228);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_262 = lean_unsigned_to_nat(0u);
x_263 = l_Lean_Expr_getAppNumArgsAux___main(x_218, x_262);
x_264 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_263);
x_265 = lean_mk_array(x_263, x_264);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_sub(x_263, x_266);
lean_dec(x_263);
lean_inc(x_218);
x_268 = l___private_Lean_Expr_3__getAppArgsAux___main(x_218, x_265, x_267);
x_269 = lean_ctor_get(x_1, 2);
lean_inc(x_269);
lean_dec(x_1);
x_270 = lean_array_get_size(x_268);
x_271 = lean_nat_dec_le(x_270, x_270);
if (x_271 == 0)
{
uint8_t x_272; 
lean_inc(x_269);
x_272 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6(x_218, x_268, x_270, x_269);
lean_dec(x_270);
lean_dec(x_268);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_274 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_273, x_218, x_269, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_269);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
lean_dec(x_274);
x_280 = lean_ctor_get(x_275, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
 x_281 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_280);
x_282 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_280, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Meta_isExprDefEqAux(x_218, x_283, x_3, x_4, x_5, x_6, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_281);
lean_dec(x_280);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
x_290 = lean_box(0);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_288);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_293 = x_285;
} else {
 lean_dec_ref(x_285);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_281;
}
lean_ctor_set(x_294, 0, x_280);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_281);
lean_dec(x_280);
x_296 = lean_ctor_get(x_285, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_298 = x_285;
} else {
 lean_dec_ref(x_285);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_300 = lean_ctor_get(x_282, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_282, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_302 = x_282;
} else {
 lean_dec_ref(x_282);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_304 = lean_ctor_get(x_274, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_274, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_306 = x_274;
} else {
 lean_dec_ref(x_274);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_269);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_219);
return x_309;
}
}
else
{
uint8_t x_310; 
lean_inc(x_269);
x_310 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7(x_218, lean_box(0), x_268, x_270, x_269);
lean_dec(x_270);
lean_dec(x_268);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_312 = l___private_Lean_Util_WHNF_2__mkNullaryCtor___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__11(x_311, x_218, x_269, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_269);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
lean_dec(x_312);
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_319 = x_313;
} else {
 lean_dec_ref(x_313);
 x_319 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_318);
x_320 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_318, x_3, x_4, x_5, x_6, x_317);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Lean_Meta_isExprDefEqAux(x_218, x_321, x_3, x_4, x_5, x_6, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_unbox(x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_319);
lean_dec(x_318);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_327 = x_323;
} else {
 lean_dec_ref(x_323);
 x_327 = lean_box(0);
}
x_328 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_326);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_323, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_331 = x_323;
} else {
 lean_dec_ref(x_323);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_319;
}
lean_ctor_set(x_332, 0, x_318);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_330);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_319);
lean_dec(x_318);
x_334 = lean_ctor_get(x_323, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_323, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_336 = x_323;
} else {
 lean_dec_ref(x_323);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = lean_ctor_get(x_320, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_320, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_340 = x_320;
} else {
 lean_dec_ref(x_320);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_342 = lean_ctor_get(x_312, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_312, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_344 = x_312;
} else {
 lean_dec_ref(x_312);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_269);
lean_dec(x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_219);
return x_347;
}
}
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_11);
if (x_348 == 0)
{
return x_11;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_11, 0);
x_350 = lean_ctor_get(x_11, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_11);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
else
{
uint8_t x_352; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_352 = !lean_is_exclusive(x_8);
if (x_352 == 0)
{
return x_8;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_8, 0);
x_354 = lean_ctor_get(x_8, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_8);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
}
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_RecursorVal_getMajorIdx(x_4);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_15 = lean_expr_eqv(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_6, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_65; 
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
x_65 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_66 = l_Lean_WHNF_toCtorIfLit(x_21);
lean_inc(x_4);
x_67 = l___private_Lean_Util_WHNF_3__getRecRuleFor(x_4, x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_68 = lean_expr_eqv(x_2, x_3);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_22);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_22);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Expr_getAppNumArgsAux___main(x_66, x_73);
x_75 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_74);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = l___private_Lean_Expr_3__getAppArgsAux___main(x_66, x_76, x_78);
x_80 = l_List_lengthAux___main___rarg(x_5, x_73);
x_81 = lean_ctor_get(x_4, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_List_lengthAux___main___rarg(x_82, x_73);
x_84 = lean_nat_dec_eq(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_85 = lean_expr_eqv(x_2, x_3);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_22);
return x_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_22);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 2);
lean_inc(x_89);
x_90 = l_Lean_Expr_instantiateLevelParams(x_89, x_82, x_5);
lean_dec(x_82);
x_91 = lean_ctor_get(x_4, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_4, 4);
lean_inc(x_92);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
x_94 = lean_ctor_get(x_4, 5);
lean_inc(x_94);
lean_dec(x_4);
x_95 = lean_nat_add(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
x_96 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_95, x_6, x_73, x_90);
lean_dec(x_95);
x_97 = lean_array_get_size(x_79);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
lean_dec(x_72);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_97, x_79, x_99, x_96);
lean_dec(x_79);
lean_dec(x_97);
x_101 = lean_nat_add(x_12, x_77);
lean_dec(x_12);
x_102 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_13, x_6, x_101, x_100);
lean_dec(x_13);
x_103 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_102, x_7, x_8, x_9, x_10, x_22);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
lean_inc(x_4);
x_104 = l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__5(x_4, x_21, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_24 = x_21;
x_25 = x_106;
goto block_64;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_21);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
x_24 = x_108;
x_25 = x_107;
goto block_64;
}
}
else
{
uint8_t x_109; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_WHNF_toCtorIfLit(x_24);
lean_inc(x_4);
x_27 = l___private_Lean_Util_WHNF_3__getRecRuleFor(x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_28 = lean_expr_eqv(x_2, x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_33);
x_35 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Lean_Expr_3__getAppArgsAux___main(x_26, x_36, x_38);
x_40 = l_List_lengthAux___main___rarg(x_5, x_33);
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_lengthAux___main___rarg(x_42, x_33);
x_44 = lean_nat_dec_eq(x_40, x_43);
lean_dec(x_43);
lean_dec(x_40);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_45 = lean_expr_eqv(x_2, x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_23)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_23;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_25);
return x_47;
}
else
{
lean_object* x_48; 
if (lean_is_scalar(x_23)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_23;
}
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_25);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
lean_dec(x_1);
x_49 = lean_ctor_get(x_32, 2);
lean_inc(x_49);
x_50 = l_Lean_Expr_instantiateLevelParams(x_49, x_42, x_5);
lean_dec(x_42);
x_51 = lean_ctor_get(x_4, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 4);
lean_inc(x_52);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_4, 5);
lean_inc(x_54);
lean_dec(x_4);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_55, x_6, x_33, x_50);
lean_dec(x_55);
x_57 = lean_array_get_size(x_39);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_57, x_39, x_59, x_56);
lean_dec(x_39);
lean_dec(x_57);
x_61 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
x_62 = l___private_Lean_Expr_2__mkAppRangeAux___main(x_13, x_6, x_61, x_60);
lean_dec(x_13);
x_63 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_62, x_7, x_8, x_9, x_10, x_25);
return x_63;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_20);
if (x_113 == 0)
{
return x_20;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_20, 0);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_20);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalDecl_value_x3f(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_7(x_11, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_7(x_10, lean_box(0), x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_13 = l_Lean_Expr_Inhabited;
x_14 = l_monadInhabited___rarg(x_1, x_13);
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_apply_5(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1___boxed), 8, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
x_21 = lean_apply_9(x_18, lean_box(0), lean_box(0), x_19, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1___boxed), 6, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__2), 8, 2);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
x_26 = lean_apply_9(x_23, lean_box(0), lean_box(0), x_24, x_25, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
case 4:
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = l_Lean_Expr_getAppFn___main(x_28);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_30 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Lean_Expr_isLambda(x_32);
if (x_34 == 0)
{
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_30);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = l_Lean_Meta_getConstNoEx_x3f(x_35, x_3, x_4, x_5, x_6, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
switch (lean_obj_tag(x_48)) {
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
x_50 = l_Lean_ConstantInfo_name(x_48);
x_51 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_50, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_51, 0, x_2);
return x_51;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_32);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_64);
x_66 = lean_mk_empty_array_with_capacity(x_65);
lean_dec(x_65);
lean_inc(x_2);
x_67 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_66);
x_68 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2(x_2, x_29, x_32, x_48, x_36, x_67, x_3, x_4, x_5, x_6, x_63);
lean_dec(x_67);
lean_dec(x_36);
lean_dec(x_48);
lean_dec(x_32);
lean_dec(x_29);
return x_68;
}
}
case 4:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
lean_dec(x_48);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_71);
x_73 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_72);
x_74 = lean_mk_array(x_72, x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_72, x_75);
lean_dec(x_72);
lean_inc(x_2);
x_77 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_74, x_76);
x_78 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3(x_2, x_29, x_32, x_70, x_36, x_77, x_3, x_4, x_5, x_6, x_69);
lean_dec(x_77);
lean_dec(x_36);
lean_dec(x_70);
lean_dec(x_32);
lean_dec(x_29);
return x_78;
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_37, 1);
lean_inc(x_79);
lean_dec(x_37);
x_80 = lean_ctor_get(x_48, 0);
lean_inc(x_80);
lean_dec(x_48);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_81);
x_83 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_82);
x_84 = lean_mk_array(x_82, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_82, x_85);
lean_dec(x_82);
lean_inc(x_2);
x_87 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_84, x_86);
x_88 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4(x_2, x_29, x_32, x_80, x_36, x_87, x_3, x_4, x_5, x_6, x_79);
lean_dec(x_87);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_29);
return x_88;
}
default: 
{
uint8_t x_89; 
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_37);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_37, 0);
lean_dec(x_90);
x_91 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_92);
return x_37;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
lean_dec(x_37);
x_94 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_32);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_expr_eqv(x_29, x_32);
lean_dec(x_29);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_Expr_updateFn___main(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_99);
return x_30;
}
else
{
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_30);
lean_dec(x_29);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_100);
x_102 = lean_mk_empty_array_with_capacity(x_101);
lean_dec(x_101);
x_103 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_102);
x_104 = l_Lean_Expr_betaRev(x_32, x_103);
lean_dec(x_103);
lean_dec(x_32);
x_105 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_104, x_3, x_4, x_5, x_6, x_33);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_30, 0);
x_107 = lean_ctor_get(x_30, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_30);
x_108 = l_Lean_Expr_isLambda(x_106);
if (x_108 == 0)
{
if (lean_obj_tag(x_106) == 4)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
x_111 = l_Lean_Meta_getConstNoEx_x3f(x_109, x_3, x_4, x_5, x_6, x_107);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_106);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_2);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
switch (lean_obj_tag(x_119)) {
case 1:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_dec(x_111);
x_121 = l_Lean_ConstantInfo_name(x_119);
x_122 = l___private_Lean_Meta_WHNF_1__isAuxDefImp_x3f(x_121, x_3, x_4, x_5, x_6, x_120);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_119);
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_126;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
return x_129;
}
else
{
lean_object* x_130; 
lean_dec(x_106);
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_125);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_dec(x_122);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_132);
x_134 = lean_mk_empty_array_with_capacity(x_133);
lean_dec(x_133);
lean_inc(x_2);
x_135 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_134);
x_136 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2(x_2, x_29, x_106, x_119, x_110, x_135, x_3, x_4, x_5, x_6, x_131);
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_119);
lean_dec(x_106);
lean_dec(x_29);
return x_136;
}
}
case 4:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_111, 1);
lean_inc(x_137);
lean_dec(x_111);
x_138 = lean_ctor_get(x_119, 0);
lean_inc(x_138);
lean_dec(x_119);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_139);
x_141 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_140, x_143);
lean_dec(x_140);
lean_inc(x_2);
x_145 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_142, x_144);
x_146 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3(x_2, x_29, x_106, x_138, x_110, x_145, x_3, x_4, x_5, x_6, x_137);
lean_dec(x_145);
lean_dec(x_110);
lean_dec(x_138);
lean_dec(x_106);
lean_dec(x_29);
return x_146;
}
case 7:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_111, 1);
lean_inc(x_147);
lean_dec(x_111);
x_148 = lean_ctor_get(x_119, 0);
lean_inc(x_148);
lean_dec(x_119);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_149);
x_151 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_150);
x_152 = lean_mk_array(x_150, x_151);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_sub(x_150, x_153);
lean_dec(x_150);
lean_inc(x_2);
x_155 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_152, x_154);
x_156 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4(x_2, x_29, x_106, x_148, x_110, x_155, x_3, x_4, x_5, x_6, x_147);
lean_dec(x_155);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_29);
return x_156;
}
default: 
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_111, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_158 = x_111;
} else {
 lean_dec_ref(x_111);
 x_158 = lean_box(0);
}
x_159 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
return x_161;
}
else
{
lean_object* x_162; 
lean_dec(x_106);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_2);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
}
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
x_163 = lean_expr_eqv(x_29, x_106);
lean_dec(x_29);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_updateFn___main(x_2, x_106);
lean_dec(x_106);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_107);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_106);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_2);
lean_ctor_set(x_166, 1, x_107);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_29);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_167);
x_169 = lean_mk_empty_array_with_capacity(x_168);
lean_dec(x_168);
x_170 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_169);
x_171 = l_Lean_Expr_betaRev(x_106, x_170);
lean_dec(x_170);
lean_dec(x_106);
x_172 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_171, x_3, x_4, x_5, x_6, x_107);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_30);
if (x_173 == 0)
{
return x_30;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_30, 0);
x_175 = lean_ctor_get(x_30, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_30);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
case 8:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_1);
x_177 = lean_ctor_get(x_2, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_2, 3);
lean_inc(x_178);
lean_dec(x_2);
x_179 = lean_expr_instantiate1(x_178, x_177);
lean_dec(x_177);
lean_dec(x_178);
x_180 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_179, x_3, x_4, x_5, x_6, x_7);
return x_180;
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
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_1);
x_183 = lean_ctor_get(x_2, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_185 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_184, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = l_Lean_Expr_getAppFn___main(x_187);
if (lean_obj_tag(x_189) == 4)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_free_object(x_185);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_Meta_getConstNoEx_x3f(x_190, x_3, x_4, x_5, x_6, x_188);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
lean_dec(x_187);
lean_dec(x_183);
x_193 = !lean_is_exclusive(x_191);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 0);
lean_dec(x_194);
lean_ctor_set(x_191, 0, x_2);
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
lean_dec(x_192);
if (lean_obj_tag(x_197) == 6)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_191);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_191, 0);
lean_dec(x_199);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
lean_dec(x_197);
x_201 = lean_ctor_get(x_200, 3);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_nat_add(x_201, x_183);
lean_dec(x_183);
lean_dec(x_201);
x_203 = lean_unsigned_to_nat(0u);
x_204 = l_Lean_Expr_getAppNumArgsAux___main(x_187, x_203);
x_205 = lean_nat_sub(x_204, x_202);
lean_dec(x_202);
lean_dec(x_204);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_sub(x_205, x_206);
lean_dec(x_205);
x_208 = l_Lean_Expr_getRevArgD___main(x_187, x_207, x_2);
lean_dec(x_2);
lean_dec(x_187);
lean_ctor_set(x_191, 0, x_208);
return x_191;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_ctor_get(x_191, 1);
lean_inc(x_209);
lean_dec(x_191);
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
lean_dec(x_197);
x_211 = lean_ctor_get(x_210, 3);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_nat_add(x_211, x_183);
lean_dec(x_183);
lean_dec(x_211);
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Lean_Expr_getAppNumArgsAux___main(x_187, x_213);
x_215 = lean_nat_sub(x_214, x_212);
lean_dec(x_212);
lean_dec(x_214);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_nat_sub(x_215, x_216);
lean_dec(x_215);
x_218 = l_Lean_Expr_getRevArgD___main(x_187, x_217, x_2);
lean_dec(x_2);
lean_dec(x_187);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_209);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_183);
x_220 = !lean_is_exclusive(x_191);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_191, 0);
lean_dec(x_221);
lean_ctor_set(x_191, 0, x_2);
return x_191;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_191, 1);
lean_inc(x_222);
lean_dec(x_191);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_2);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
else
{
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_185, 0, x_2);
return x_185;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_185, 0);
x_225 = lean_ctor_get(x_185, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_185);
x_226 = l_Lean_Expr_getAppFn___main(x_224);
if (lean_obj_tag(x_226) == 4)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_Lean_Meta_getConstNoEx_x3f(x_227, x_3, x_4, x_5, x_6, x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_224);
lean_dec(x_183);
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
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
lean_dec(x_229);
if (lean_obj_tag(x_233) == 6)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_235 = x_228;
} else {
 lean_dec_ref(x_228);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_236, 3);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_nat_add(x_237, x_183);
lean_dec(x_183);
lean_dec(x_237);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Lean_Expr_getAppNumArgsAux___main(x_224, x_239);
x_241 = lean_nat_sub(x_240, x_238);
lean_dec(x_238);
lean_dec(x_240);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_sub(x_241, x_242);
lean_dec(x_241);
x_244 = l_Lean_Expr_getRevArgD___main(x_224, x_243, x_2);
lean_dec(x_2);
lean_dec(x_224);
if (lean_is_scalar(x_235)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_235;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_234);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_233);
lean_dec(x_224);
lean_dec(x_183);
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_247 = x_228;
} else {
 lean_dec_ref(x_228);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_2);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_225);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_185);
if (x_250 == 0)
{
return x_185;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_185, 0);
x_252 = lean_ctor_get(x_185, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_185);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
case 12:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_2);
x_254 = l_Lean_Expr_Inhabited;
x_255 = l_monadInhabited___rarg(x_1, x_254);
x_256 = l_unreachable_x21___rarg(x_255);
x_257 = lean_apply_5(x_256, x_3, x_4, x_5, x_6, x_7);
return x_257;
}
default: 
{
lean_object* x_258; 
x_258 = lean_box(0);
x_8 = x_258;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_7(x_10, lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
lean_object* l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_8 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_WHNF_3__whnfCoreImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_WHNF_8__deltaBetaDefinition___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_WHNF_reduceQuotRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_WHNF_reduceRec___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_whnfEasyCases___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_whnfCore___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_WHNF_3__whnfCoreImp), 6, 1);
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
lean_object* l_Lean_Meta_reduceNativeConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Environment_evalConstCheck___rarg(x_12, x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_16, x_3, x_4, x_5, x_6, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Environment_evalConstCheck___rarg(x_21, x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_25, x_3, x_4, x_5, x_6, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_reduceNativeConst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNativeConst___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_reduceNativeConst___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceNativeConst___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_reduceBoolNativeUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_boolToExpr___lambda__1___closed__2;
x_8 = l_Lean_Meta_reduceNativeConst___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
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
x_8 = l_Lean_Meta_reduceNativeConst___rarg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
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
x_2 = l_Lean_Exception_inhabited___closed__1;
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
x_2 = l_Lean_Exception_inhabited___closed__1;
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
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBool");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceNat");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Meta_reduceNative_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_boolToExpr___lambda__1___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceNative_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_boolToExpr___lambda__1___closed__6;
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
lean_object* l_Lean_Meta_withNatValue___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_21 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_33 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_20 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_34 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("whnf");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceBinOp");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__2;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" op ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__7;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__10;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceBinNatOp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_2 = l_Lean_Meta_reduceBinNatOp___closed__7;
x_3 = lean_alloc_ctor(9, 2, 0);
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
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_25 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_15);
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
x_65 = lean_ctor_get(x_64, 2);
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
x_70 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_71 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_70, x_4, x_5, x_6, x_7, x_69);
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
x_47 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_48 = l_Lean_Meta_reduceBinNatOp___closed__12;
x_49 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_47, x_48, x_4, x_5, x_6, x_7, x_41);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
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
x_124 = lean_st_ref_get(x_7, x_94);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 2);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get_uint8(x_126, sizeof(void*)*1);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_129 = 0;
x_97 = x_129;
x_98 = x_128;
goto block_123;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_dec(x_124);
x_131 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_132 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_131, x_4, x_5, x_6, x_7, x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_unbox(x_133);
lean_dec(x_133);
x_97 = x_135;
x_98 = x_134;
goto block_123;
}
block_123:
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
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_95);
lean_inc(x_96);
x_104 = l_Nat_repr(x_96);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_110 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_109, x_108, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_apply_2(x_1, x_113, x_96);
x_115 = l_Lean_mkNatLit(x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_110, 0, x_116);
return x_110;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_apply_2(x_1, x_118, x_96);
x_120 = l_Lean_mkNatLit(x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_25);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_25, 0);
lean_dec(x_137);
x_138 = lean_box(0);
lean_ctor_set(x_25, 0, x_138);
return x_25;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_25, 1);
lean_inc(x_139);
lean_dec(x_25);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
default: 
{
uint8_t x_142; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_25);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_25, 0);
lean_dec(x_143);
x_144 = lean_box(0);
lean_ctor_set(x_25, 0, x_144);
return x_25;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_25, 1);
lean_inc(x_145);
lean_dec(x_25);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_25);
if (x_148 == 0)
{
return x_25;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_25, 0);
x_150 = lean_ctor_get(x_25, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_25);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_9, 1);
lean_inc(x_152);
lean_dec(x_9);
x_153 = lean_ctor_get(x_11, 1);
lean_inc(x_153);
lean_dec(x_11);
x_154 = lean_ctor_get(x_12, 1);
lean_inc(x_154);
lean_dec(x_12);
x_155 = l_Lean_Literal_type___closed__1;
x_156 = lean_string_dec_eq(x_154, x_155);
lean_dec(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_153);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_152);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_WHNF_toCtorIfLit___closed__4;
x_160 = lean_string_dec_eq(x_153, x_159);
lean_dec(x_153);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_152);
return x_162;
}
else
{
lean_object* x_163; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_163 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_152);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
switch (lean_obj_tag(x_164)) {
case 4:
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
if (lean_obj_tag(x_165) == 1)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 1)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_169 = x_163;
} else {
 lean_dec_ref(x_163);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_string_dec_eq(x_171, x_155);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_173 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
else
{
uint8_t x_175; 
x_175 = lean_string_dec_eq(x_170, x_159);
lean_dec(x_170);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_176 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_169;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_168);
return x_177;
}
else
{
uint8_t x_178; lean_object* x_179; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_st_ref_get(x_7, x_168);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 2);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_ctor_get_uint8(x_198, sizeof(void*)*1);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_dec(x_196);
x_201 = 0;
x_178 = x_201;
x_179 = x_200;
goto block_195;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
x_203 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_204 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_203, x_4, x_5, x_6, x_7, x_202);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_unbox(x_205);
lean_dec(x_205);
x_178 = x_207;
x_179 = x_206;
goto block_195;
}
block_195:
{
if (x_178 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_180 = lean_unsigned_to_nat(0u);
x_181 = lean_apply_2(x_1, x_180, x_180);
x_182 = l_Lean_mkNatLit(x_181);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_169)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_169;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_169);
x_185 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_186 = l_Lean_Meta_reduceBinNatOp___closed__12;
x_187 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_185, x_186, x_4, x_5, x_6, x_7, x_179);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_apply_2(x_1, x_190, x_190);
x_192 = l_Lean_mkNatLit(x_191);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
return x_194;
}
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_208 = lean_ctor_get(x_163, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_209 = x_163;
} else {
 lean_dec_ref(x_163);
 x_209 = lean_box(0);
}
x_210 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = lean_ctor_get(x_163, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_213 = x_163;
} else {
 lean_dec_ref(x_163);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_216 = lean_ctor_get(x_163, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_217 = x_163;
} else {
 lean_dec_ref(x_163);
 x_217 = lean_box(0);
}
x_218 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
}
case 9:
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_164, 0);
lean_inc(x_220);
lean_dec(x_164);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_221 = lean_ctor_get(x_163, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_222 = x_163;
} else {
 lean_dec_ref(x_163);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
lean_dec(x_220);
x_246 = lean_st_ref_get(x_7, x_221);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 2);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_ctor_get_uint8(x_248, sizeof(void*)*1);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = 0;
x_224 = x_251;
x_225 = x_250;
goto block_245;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
lean_dec(x_246);
x_253 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_254 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_253, x_4, x_5, x_6, x_7, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_unbox(x_255);
lean_dec(x_255);
x_224 = x_257;
x_225 = x_256;
goto block_245;
}
block_245:
{
if (x_224 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_226 = lean_unsigned_to_nat(0u);
x_227 = lean_apply_2(x_1, x_226, x_223);
x_228 = l_Lean_mkNatLit(x_227);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
if (lean_is_scalar(x_222)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_222;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_225);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_222);
lean_inc(x_223);
x_231 = l_Nat_repr(x_223);
x_232 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Lean_Meta_reduceBinNatOp___closed__11;
x_235 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_237 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_236, x_235, x_4, x_5, x_6, x_7, x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = lean_unsigned_to_nat(0u);
x_241 = lean_apply_2(x_1, x_240, x_223);
x_242 = l_Lean_mkNatLit(x_241);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_238);
return x_244;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_220);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_258 = lean_ctor_get(x_163, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_259 = x_163;
} else {
 lean_dec_ref(x_163);
 x_259 = lean_box(0);
}
x_260 = lean_box(0);
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_258);
return x_261;
}
}
default: 
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_164);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_262 = lean_ctor_get(x_163, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_263 = x_163;
} else {
 lean_dec_ref(x_163);
 x_263 = lean_box(0);
}
x_264 = lean_box(0);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_263;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_262);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_266 = lean_ctor_get(x_163, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_163, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_268 = x_163;
} else {
 lean_dec_ref(x_163);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_9);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_9, 0);
lean_dec(x_271);
x_272 = lean_box(0);
lean_ctor_set(x_9, 0, x_272);
return x_9;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_9, 1);
lean_inc(x_273);
lean_dec(x_9);
x_274 = lean_box(0);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_9);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_9, 0);
lean_dec(x_277);
x_278 = lean_box(0);
lean_ctor_set(x_9, 0, x_278);
return x_9;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_9, 1);
lean_inc(x_279);
lean_dec(x_9);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_282 = !lean_is_exclusive(x_9);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_9, 0);
lean_dec(x_283);
x_284 = lean_box(0);
lean_ctor_set(x_9, 0, x_284);
return x_9;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_9, 1);
lean_inc(x_285);
lean_dec(x_9);
x_286 = lean_box(0);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
}
case 9:
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_10, 0);
lean_inc(x_288);
lean_dec(x_10);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_9, 1);
lean_inc(x_289);
lean_dec(x_9);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_291 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_289);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
switch (lean_obj_tag(x_292)) {
case 4:
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
if (lean_obj_tag(x_293) == 1)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
if (lean_obj_tag(x_294) == 1)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_296 = lean_ctor_get(x_291, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_297 = x_291;
} else {
 lean_dec_ref(x_291);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_dec(x_293);
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_dec(x_294);
x_300 = l_Lean_Literal_type___closed__1;
x_301 = lean_string_dec_eq(x_299, x_300);
lean_dec(x_299);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_298);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_302 = lean_box(0);
if (lean_is_scalar(x_297)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_297;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_296);
return x_303;
}
else
{
lean_object* x_304; uint8_t x_305; 
x_304 = l_Lean_WHNF_toCtorIfLit___closed__4;
x_305 = lean_string_dec_eq(x_298, x_304);
lean_dec(x_298);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_306 = lean_box(0);
if (lean_is_scalar(x_297)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_297;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_296);
return x_307;
}
else
{
uint8_t x_308; lean_object* x_309; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_337 = lean_st_ref_get(x_7, x_296);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_338, 2);
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_ctor_get_uint8(x_339, sizeof(void*)*1);
lean_dec(x_339);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
lean_dec(x_337);
x_342 = 0;
x_308 = x_342;
x_309 = x_341;
goto block_336;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_343 = lean_ctor_get(x_337, 1);
lean_inc(x_343);
lean_dec(x_337);
x_344 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_345 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_344, x_4, x_5, x_6, x_7, x_343);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_unbox(x_346);
lean_dec(x_346);
x_308 = x_348;
x_309 = x_347;
goto block_336;
}
block_336:
{
if (x_308 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_apply_2(x_1, x_290, x_310);
x_312 = l_Lean_mkNatLit(x_311);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
if (lean_is_scalar(x_297)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_297;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
return x_314;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_297);
lean_inc(x_290);
x_315 = l_Nat_repr(x_290);
x_316 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = l_Lean_Meta_reduceBinNatOp___closed__10;
x_319 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Meta_reduceBinNatOp___closed__7;
x_321 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_323 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_322, x_321, x_4, x_5, x_6, x_7, x_309);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_323, 0);
lean_dec(x_325);
x_326 = lean_unsigned_to_nat(0u);
x_327 = lean_apply_2(x_1, x_290, x_326);
x_328 = l_Lean_mkNatLit(x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_323, 0, x_329);
return x_323;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_ctor_get(x_323, 1);
lean_inc(x_330);
lean_dec(x_323);
x_331 = lean_unsigned_to_nat(0u);
x_332 = lean_apply_2(x_1, x_290, x_331);
x_333 = l_Lean_mkNatLit(x_332);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_330);
return x_335;
}
}
}
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_291);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_291, 0);
lean_dec(x_350);
x_351 = lean_box(0);
lean_ctor_set(x_291, 0, x_351);
return x_291;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_291, 1);
lean_inc(x_352);
lean_dec(x_291);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
else
{
uint8_t x_355; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_355 = !lean_is_exclusive(x_291);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_291, 0);
lean_dec(x_356);
x_357 = lean_box(0);
lean_ctor_set(x_291, 0, x_357);
return x_291;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_291, 1);
lean_inc(x_358);
lean_dec(x_291);
x_359 = lean_box(0);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_293);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_291);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_291, 0);
lean_dec(x_362);
x_363 = lean_box(0);
lean_ctor_set(x_291, 0, x_363);
return x_291;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_291, 1);
lean_inc(x_364);
lean_dec(x_291);
x_365 = lean_box(0);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
}
case 9:
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_292, 0);
lean_inc(x_367);
lean_dec(x_292);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_368 = lean_ctor_get(x_291, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_369 = x_291;
} else {
 lean_dec_ref(x_291);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_367, 0);
lean_inc(x_370);
lean_dec(x_367);
x_399 = lean_st_ref_get(x_7, x_368);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_400, 2);
lean_inc(x_401);
lean_dec(x_400);
x_402 = lean_ctor_get_uint8(x_401, sizeof(void*)*1);
lean_dec(x_401);
if (x_402 == 0)
{
lean_object* x_403; uint8_t x_404; 
x_403 = lean_ctor_get(x_399, 1);
lean_inc(x_403);
lean_dec(x_399);
x_404 = 0;
x_371 = x_404;
x_372 = x_403;
goto block_398;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_405 = lean_ctor_get(x_399, 1);
lean_inc(x_405);
lean_dec(x_399);
x_406 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_407 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_406, x_4, x_5, x_6, x_7, x_405);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_unbox(x_408);
lean_dec(x_408);
x_371 = x_410;
x_372 = x_409;
goto block_398;
}
block_398:
{
if (x_371 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_373 = lean_apply_2(x_1, x_290, x_370);
x_374 = l_Lean_mkNatLit(x_373);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
if (lean_is_scalar(x_369)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_369;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_372);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
lean_dec(x_369);
lean_inc(x_290);
x_377 = l_Nat_repr(x_290);
x_378 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_378, 0, x_377);
x_379 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_379, 0, x_378);
x_380 = l_Lean_Meta_reduceBinNatOp___closed__10;
x_381 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
lean_inc(x_370);
x_382 = l_Nat_repr(x_370);
x_383 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_383, 0, x_382);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_383);
x_385 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_385, 0, x_381);
lean_ctor_set(x_385, 1, x_384);
x_386 = l_Lean_Meta_reduceBinNatOp___closed__4;
x_387 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__3(x_386, x_385, x_4, x_5, x_6, x_7, x_372);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_389 = lean_ctor_get(x_387, 0);
lean_dec(x_389);
x_390 = lean_apply_2(x_1, x_290, x_370);
x_391 = l_Lean_mkNatLit(x_390);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_387, 0, x_392);
return x_387;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_393 = lean_ctor_get(x_387, 1);
lean_inc(x_393);
lean_dec(x_387);
x_394 = lean_apply_2(x_1, x_290, x_370);
x_395 = l_Lean_mkNatLit(x_394);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_393);
return x_397;
}
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_367);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_291);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_291, 0);
lean_dec(x_412);
x_413 = lean_box(0);
lean_ctor_set(x_291, 0, x_413);
return x_291;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_291, 1);
lean_inc(x_414);
lean_dec(x_291);
x_415 = lean_box(0);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_414);
return x_416;
}
}
}
default: 
{
uint8_t x_417; 
lean_dec(x_292);
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_291);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_291, 0);
lean_dec(x_418);
x_419 = lean_box(0);
lean_ctor_set(x_291, 0, x_419);
return x_291;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_291, 1);
lean_inc(x_420);
lean_dec(x_291);
x_421 = lean_box(0);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
}
}
else
{
uint8_t x_423; 
lean_dec(x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_423 = !lean_is_exclusive(x_291);
if (x_423 == 0)
{
return x_291;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_291, 0);
x_425 = lean_ctor_get(x_291, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_291);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
else
{
uint8_t x_427; 
lean_dec(x_288);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_9);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_9, 0);
lean_dec(x_428);
x_429 = lean_box(0);
lean_ctor_set(x_9, 0, x_429);
return x_9;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_9, 1);
lean_inc(x_430);
lean_dec(x_9);
x_431 = lean_box(0);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
default: 
{
uint8_t x_433; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_433 = !lean_is_exclusive(x_9);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_9, 0);
lean_dec(x_434);
x_435 = lean_box(0);
lean_ctor_set(x_9, 0, x_435);
return x_9;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_9, 1);
lean_inc(x_436);
lean_dec(x_9);
x_437 = lean_box(0);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_9);
if (x_439 == 0)
{
return x_9;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_9, 0);
x_441 = lean_ctor_get(x_9, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_9);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
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
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_25 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_15);
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
x_118 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_122 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_111);
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
x_200 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_3, x_4, x_5, x_6, x_7, x_198);
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
x_212 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
x_227 = l_Lean_WHNF_toCtorIfLit___closed__4;
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
lean_object* l_Lean_Meta_reduceNat_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reduceNat_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sub");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mul");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("div");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mod");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("beq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ble");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_reduceNat_x3f___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_ble___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_reduceNat_x3f___closed__17() {
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
x_12 = l_Lean_WHNF_toCtorIfLit___closed__2;
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
x_42 = l_Nat_HasMod___closed__1;
x_43 = l_Lean_Meta_reduceBinNatOp(x_42, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_21);
x_44 = l_Nat_HasDiv___closed__1;
x_45 = l_Lean_Meta_reduceBinNatOp(x_44, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = l_Nat_HasMul___closed__1;
x_47 = l_Lean_Meta_reduceBinNatOp(x_46, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
x_48 = l_Nat_HasSub___closed__1;
x_49 = l_Lean_Meta_reduceBinNatOp(x_48, x_20, x_19, x_2, x_3, x_4, x_5, x_6);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_21);
x_50 = l_Nat_HasAdd___closed__1;
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
lean_object* l___private_Lean_Meta_WHNF_4__useWHNFCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasFVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_8, 5);
x_10 = 2;
x_11 = l_Lean_Meta_TransparencyMode_beq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
lean_object* l___private_Lean_Meta_WHNF_4__useWHNFCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_WHNF_4__useWHNFCache(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_WHNF_5__cached_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_16, x_2);
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
x_22 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_21, x_2);
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
x_28 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_27, x_2);
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
x_33 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_32, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_37 = l_unreachable_x21___rarg(x_36);
x_38 = lean_apply_5(x_37, x_3, x_4, x_5, x_6, x_35);
return x_38;
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_5__cached_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_5__cached_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_WHNF_6__cache(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_20 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_19, x_2, x_3);
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
x_31 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_30, x_2, x_3);
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
x_45 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_43, x_2, x_3);
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
x_60 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_59, x_2, x_3);
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
x_69 = lean_ctor_get(x_54, 3);
x_70 = lean_ctor_get(x_54, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
lean_inc(x_3);
x_71 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_69, x_2, x_3);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_70);
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
x_82 = lean_ctor_get(x_54, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_54, 4);
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
x_85 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__4(x_82, x_2, x_3);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set(x_86, 4, x_83);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_2);
x_92 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_93 = l_unreachable_x21___rarg(x_92);
x_94 = lean_apply_5(x_93, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_3);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_3);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_94);
if (x_99 == 0)
{
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_WHNF_6__cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_WHNF_6__cache(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* _init_l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_2);
x_11 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_LocalDecl_value_x3f(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_16; 
lean_free_object(x_11);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_16;
x_6 = x_14;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = l_Lean_LocalDecl_value_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_1 = x_22;
x_6 = x_19;
goto _start;
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
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_28, x_2, x_3, x_4, x_5, x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_1 = x_36;
x_6 = x_35;
goto _start;
}
}
case 4:
{
uint8_t x_38; lean_object* x_39; uint8_t x_108; 
x_108 = l_Lean_Expr_hasFVar(x_1);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_109, 5);
lean_dec(x_109);
x_111 = 2;
x_112 = l_Lean_Meta_TransparencyMode_beq(x_110, x_111);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = 1;
x_38 = x_113;
x_39 = x_6;
goto block_107;
}
else
{
uint8_t x_114; 
x_114 = 0;
x_38 = x_114;
x_39 = x_6;
goto block_107;
}
}
else
{
uint8_t x_115; 
x_115 = 0;
x_38 = x_115;
x_39 = x_6;
goto block_107;
}
block_107:
{
lean_object* x_40; lean_object* x_41; 
if (x_38 == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
x_40 = x_83;
x_41 = x_39;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_st_ref_get(x_3, x_39);
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_85, 5);
lean_dec(x_85);
switch (x_86) {
case 0:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 4);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_90, x_1);
x_40 = x_91;
x_41 = x_88;
goto block_82;
}
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_dec(x_84);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_94, 3);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_95, x_1);
x_40 = x_96;
x_41 = x_93;
goto block_82;
}
default: 
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_dec(x_84);
x_98 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_99 = l_unreachable_x21___rarg(x_98);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_100 = lean_apply_5(x_99, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_40 = x_101;
x_41 = x_102;
goto block_82;
}
else
{
uint8_t x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
block_82:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_43);
x_45 = l_Lean_Meta_reduceNat_x3f(x_43, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_43);
x_48 = l_Lean_Meta_reduceNative_x3f(x_43, x_2, x_3, x_4, x_5, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_43);
x_51 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_43, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l___private_Lean_Meta_WHNF_6__cache(x_38, x_1, x_43, x_2, x_3, x_4, x_5, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_1);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_1 = x_56;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
lean_dec(x_49);
x_64 = l___private_Lean_Meta_WHNF_6__cache(x_38, x_1, x_63, x_2, x_3, x_4, x_5, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
return x_48;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_48);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_43);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_dec(x_45);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
lean_dec(x_46);
x_71 = l___private_Lean_Meta_WHNF_6__cache(x_38, x_1, x_70, x_2, x_3, x_4, x_5, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
return x_45;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_45, 0);
x_74 = lean_ctor_get(x_45, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_45);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_42);
if (x_76 == 0)
{
return x_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_42, 0);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_42);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_40, 0);
lean_inc(x_80);
lean_dec(x_40);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_41);
return x_81;
}
}
}
}
case 5:
{
uint8_t x_116; lean_object* x_117; uint8_t x_186; 
x_186 = l_Lean_Expr_hasFVar(x_1);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_2, 0);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_187, 5);
lean_dec(x_187);
x_189 = 2;
x_190 = l_Lean_Meta_TransparencyMode_beq(x_188, x_189);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = 1;
x_116 = x_191;
x_117 = x_6;
goto block_185;
}
else
{
uint8_t x_192; 
x_192 = 0;
x_116 = x_192;
x_117 = x_6;
goto block_185;
}
}
else
{
uint8_t x_193; 
x_193 = 0;
x_116 = x_193;
x_117 = x_6;
goto block_185;
}
block_185:
{
lean_object* x_118; lean_object* x_119; 
if (x_116 == 0)
{
lean_object* x_161; 
x_161 = lean_box(0);
x_118 = x_161;
x_119 = x_117;
goto block_160;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_st_ref_get(x_3, x_117);
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_163, 5);
lean_dec(x_163);
switch (x_164) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_167, 4);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_168, x_1);
x_118 = x_169;
x_119 = x_166;
goto block_160;
}
case 1:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
lean_dec(x_162);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_172, 3);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_173, x_1);
x_118 = x_174;
x_119 = x_171;
goto block_160;
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_162, 1);
lean_inc(x_175);
lean_dec(x_162);
x_176 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_177 = l_unreachable_x21___rarg(x_176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_178 = lean_apply_5(x_177, x_2, x_3, x_4, x_5, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_118 = x_179;
x_119 = x_180;
goto block_160;
}
else
{
uint8_t x_181; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
return x_178;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_178, 0);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_178);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
block_160:
{
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_120; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_120 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_121);
x_123 = l_Lean_Meta_reduceNat_x3f(x_121, x_2, x_3, x_4, x_5, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_121);
x_126 = l_Lean_Meta_reduceNative_x3f(x_121, x_2, x_3, x_4, x_5, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_121);
x_129 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_121, x_2, x_3, x_4, x_5, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l___private_Lean_Meta_WHNF_6__cache(x_116, x_1, x_121, x_2, x_3, x_4, x_5, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_121);
lean_dec(x_1);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
lean_dec(x_130);
x_1 = x_134;
x_6 = x_133;
goto _start;
}
}
else
{
uint8_t x_136; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_129);
if (x_136 == 0)
{
return x_129;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_129, 0);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_129);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_121);
x_140 = lean_ctor_get(x_126, 1);
lean_inc(x_140);
lean_dec(x_126);
x_141 = lean_ctor_get(x_127, 0);
lean_inc(x_141);
lean_dec(x_127);
x_142 = l___private_Lean_Meta_WHNF_6__cache(x_116, x_1, x_141, x_2, x_3, x_4, x_5, x_140);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_126);
if (x_143 == 0)
{
return x_126;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_126, 0);
x_145 = lean_ctor_get(x_126, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_126);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_121);
x_147 = lean_ctor_get(x_123, 1);
lean_inc(x_147);
lean_dec(x_123);
x_148 = lean_ctor_get(x_124, 0);
lean_inc(x_148);
lean_dec(x_124);
x_149 = l___private_Lean_Meta_WHNF_6__cache(x_116, x_1, x_148, x_2, x_3, x_4, x_5, x_147);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_123);
if (x_150 == 0)
{
return x_123;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_123, 0);
x_152 = lean_ctor_get(x_123, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_123);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_120);
if (x_154 == 0)
{
return x_120;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_120, 0);
x_156 = lean_ctor_get(x_120, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_120);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_118, 0);
lean_inc(x_158);
lean_dec(x_118);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_119);
return x_159;
}
}
}
}
case 8:
{
uint8_t x_194; lean_object* x_195; uint8_t x_264; 
x_264 = l_Lean_Expr_hasFVar(x_1);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_2, 0);
lean_inc(x_265);
x_266 = lean_ctor_get_uint8(x_265, 5);
lean_dec(x_265);
x_267 = 2;
x_268 = l_Lean_Meta_TransparencyMode_beq(x_266, x_267);
if (x_268 == 0)
{
uint8_t x_269; 
x_269 = 1;
x_194 = x_269;
x_195 = x_6;
goto block_263;
}
else
{
uint8_t x_270; 
x_270 = 0;
x_194 = x_270;
x_195 = x_6;
goto block_263;
}
}
else
{
uint8_t x_271; 
x_271 = 0;
x_194 = x_271;
x_195 = x_6;
goto block_263;
}
block_263:
{
lean_object* x_196; lean_object* x_197; 
if (x_194 == 0)
{
lean_object* x_239; 
x_239 = lean_box(0);
x_196 = x_239;
x_197 = x_195;
goto block_238;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = lean_st_ref_get(x_3, x_195);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_241, 5);
lean_dec(x_241);
switch (x_242) {
case 0:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_245, 4);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_246, x_1);
x_196 = x_247;
x_197 = x_244;
goto block_238;
}
case 1:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_240, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_240, 1);
lean_inc(x_249);
lean_dec(x_240);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_ctor_get(x_250, 3);
lean_inc(x_251);
lean_dec(x_250);
x_252 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_251, x_1);
x_196 = x_252;
x_197 = x_249;
goto block_238;
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_240, 1);
lean_inc(x_253);
lean_dec(x_240);
x_254 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_255 = l_unreachable_x21___rarg(x_254);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_256 = lean_apply_5(x_255, x_2, x_3, x_4, x_5, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_196 = x_257;
x_197 = x_258;
goto block_238;
}
else
{
uint8_t x_259; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
return x_256;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_256, 0);
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_256);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
}
}
block_238:
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_198; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_198 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_199);
x_201 = l_Lean_Meta_reduceNat_x3f(x_199, x_2, x_3, x_4, x_5, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_199);
x_204 = l_Lean_Meta_reduceNative_x3f(x_199, x_2, x_3, x_4, x_5, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_199);
x_207 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_199, x_2, x_3, x_4, x_5, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l___private_Lean_Meta_WHNF_6__cache(x_194, x_1, x_199, x_2, x_3, x_4, x_5, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_199);
lean_dec(x_1);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
lean_dec(x_208);
x_1 = x_212;
x_6 = x_211;
goto _start;
}
}
else
{
uint8_t x_214; 
lean_dec(x_199);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_207);
if (x_214 == 0)
{
return x_207;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_207, 0);
x_216 = lean_ctor_get(x_207, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_207);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_199);
x_218 = lean_ctor_get(x_204, 1);
lean_inc(x_218);
lean_dec(x_204);
x_219 = lean_ctor_get(x_205, 0);
lean_inc(x_219);
lean_dec(x_205);
x_220 = l___private_Lean_Meta_WHNF_6__cache(x_194, x_1, x_219, x_2, x_3, x_4, x_5, x_218);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_dec(x_199);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_204);
if (x_221 == 0)
{
return x_204;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_204, 0);
x_223 = lean_ctor_get(x_204, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_204);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_199);
x_225 = lean_ctor_get(x_201, 1);
lean_inc(x_225);
lean_dec(x_201);
x_226 = lean_ctor_get(x_202, 0);
lean_inc(x_226);
lean_dec(x_202);
x_227 = l___private_Lean_Meta_WHNF_6__cache(x_194, x_1, x_226, x_2, x_3, x_4, x_5, x_225);
return x_227;
}
}
else
{
uint8_t x_228; 
lean_dec(x_199);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_201);
if (x_228 == 0)
{
return x_201;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_201, 0);
x_230 = lean_ctor_get(x_201, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_201);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_198);
if (x_232 == 0)
{
return x_198;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_198, 0);
x_234 = lean_ctor_get(x_198, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_198);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_ctor_get(x_196, 0);
lean_inc(x_236);
lean_dec(x_196);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_197);
return x_237;
}
}
}
}
case 10:
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_1, 1);
lean_inc(x_272);
lean_dec(x_1);
x_1 = x_272;
goto _start;
}
case 11:
{
uint8_t x_274; lean_object* x_275; uint8_t x_344; 
x_344 = l_Lean_Expr_hasFVar(x_1);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_2, 0);
lean_inc(x_345);
x_346 = lean_ctor_get_uint8(x_345, 5);
lean_dec(x_345);
x_347 = 2;
x_348 = l_Lean_Meta_TransparencyMode_beq(x_346, x_347);
if (x_348 == 0)
{
uint8_t x_349; 
x_349 = 1;
x_274 = x_349;
x_275 = x_6;
goto block_343;
}
else
{
uint8_t x_350; 
x_350 = 0;
x_274 = x_350;
x_275 = x_6;
goto block_343;
}
}
else
{
uint8_t x_351; 
x_351 = 0;
x_274 = x_351;
x_275 = x_6;
goto block_343;
}
block_343:
{
lean_object* x_276; lean_object* x_277; 
if (x_274 == 0)
{
lean_object* x_319; 
x_319 = lean_box(0);
x_276 = x_319;
x_277 = x_275;
goto block_318;
}
else
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_320 = lean_st_ref_get(x_3, x_275);
x_321 = lean_ctor_get(x_2, 0);
lean_inc(x_321);
x_322 = lean_ctor_get_uint8(x_321, 5);
lean_dec(x_321);
switch (x_322) {
case 0:
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_323 = lean_ctor_get(x_320, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
lean_dec(x_320);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_325, 4);
lean_inc(x_326);
lean_dec(x_325);
x_327 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_326, x_1);
x_276 = x_327;
x_277 = x_324;
goto block_318;
}
case 1:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_320, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_320, 1);
lean_inc(x_329);
lean_dec(x_320);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_330, 3);
lean_inc(x_331);
lean_dec(x_330);
x_332 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_10__checkInferTypeCache___spec__1(x_331, x_1);
x_276 = x_332;
x_277 = x_329;
goto block_318;
}
default: 
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_320, 1);
lean_inc(x_333);
lean_dec(x_320);
x_334 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_335 = l_unreachable_x21___rarg(x_334);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_336 = lean_apply_5(x_335, x_2, x_3, x_4, x_5, x_333);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_276 = x_337;
x_277 = x_338;
goto block_318;
}
else
{
uint8_t x_339; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_336);
if (x_339 == 0)
{
return x_336;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_336, 0);
x_341 = lean_ctor_get(x_336, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_336);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
}
}
block_318:
{
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_278; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_278 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_279);
x_281 = l_Lean_Meta_reduceNat_x3f(x_279, x_2, x_3, x_4, x_5, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_279);
x_284 = l_Lean_Meta_reduceNative_x3f(x_279, x_2, x_3, x_4, x_5, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_279);
x_287 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_279, x_2, x_3, x_4, x_5, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l___private_Lean_Meta_WHNF_6__cache(x_274, x_1, x_279, x_2, x_3, x_4, x_5, x_289);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_279);
lean_dec(x_1);
x_291 = lean_ctor_get(x_287, 1);
lean_inc(x_291);
lean_dec(x_287);
x_292 = lean_ctor_get(x_288, 0);
lean_inc(x_292);
lean_dec(x_288);
x_1 = x_292;
x_6 = x_291;
goto _start;
}
}
else
{
uint8_t x_294; 
lean_dec(x_279);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_287);
if (x_294 == 0)
{
return x_287;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_287, 0);
x_296 = lean_ctor_get(x_287, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_287);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_279);
x_298 = lean_ctor_get(x_284, 1);
lean_inc(x_298);
lean_dec(x_284);
x_299 = lean_ctor_get(x_285, 0);
lean_inc(x_299);
lean_dec(x_285);
x_300 = l___private_Lean_Meta_WHNF_6__cache(x_274, x_1, x_299, x_2, x_3, x_4, x_5, x_298);
return x_300;
}
}
else
{
uint8_t x_301; 
lean_dec(x_279);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_284);
if (x_301 == 0)
{
return x_284;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_284, 0);
x_303 = lean_ctor_get(x_284, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_284);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_279);
x_305 = lean_ctor_get(x_281, 1);
lean_inc(x_305);
lean_dec(x_281);
x_306 = lean_ctor_get(x_282, 0);
lean_inc(x_306);
lean_dec(x_282);
x_307 = l___private_Lean_Meta_WHNF_6__cache(x_274, x_1, x_306, x_2, x_3, x_4, x_5, x_305);
return x_307;
}
}
else
{
uint8_t x_308; 
lean_dec(x_279);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_281);
if (x_308 == 0)
{
return x_281;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_281, 0);
x_310 = lean_ctor_get(x_281, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_281);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_278);
if (x_312 == 0)
{
return x_278;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_278, 0);
x_314 = lean_ctor_get(x_278, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_278);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_316 = lean_ctor_get(x_276, 0);
lean_inc(x_316);
lean_dec(x_276);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_277);
return x_317;
}
}
}
}
case 12:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_1);
x_352 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_353 = l_unreachable_x21___rarg(x_352);
x_354 = lean_apply_5(x_353, x_2, x_3, x_4, x_5, x_6);
return x_354;
}
default: 
{
lean_object* x_355; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_1);
lean_ctor_set(x_355, 1, x_6);
return x_355;
}
}
}
}
lean_object* l_Lean_Meta_whnfImpl___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_whnfImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_setWHNFRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImpl), 6, 0);
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
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_getAppFn___main(x_10);
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
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_23);
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
x_32 = l_Lean_Expr_getRevArg_x21___main(x_10, x_31);
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
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_36);
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
x_45 = l_Lean_Expr_getRevArg_x21___main(x_10, x_44);
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
x_58 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_57);
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
x_67 = l_Lean_Expr_getRevArg_x21___main(x_10, x_66);
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
x_75 = l_Lean_Expr_getAppFn___main(x_73);
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
x_89 = l_Lean_Expr_getAppNumArgsAux___main(x_73, x_88);
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
x_98 = l_Lean_Expr_getRevArg_x21___main(x_73, x_97);
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
lean_object* l_Lean_Meta_whnfHeadPredAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_19 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_9, x_3, x_4, x_5, x_6, x_18);
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
x_27 = l_Lean_Meta_whnfHeadPredAux___main(x_1, x_26, x_3, x_4, x_5, x_6, x_25);
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
lean_object* _init_l_Lean_Meta_whnfHeadPredAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_whnfHeadPredAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment_x3f___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredAux___main___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_10 = l_Lean_Meta_whnfHeadPredAux___main___closed__1;
x_11 = l_Lean_Meta_whnfHeadPredAux___main___closed__2;
x_12 = l_Lean_WHNF_whnfEasyCases___main___rarg(x_9, x_10, x_11, x_2, x_8);
x_13 = lean_apply_5(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPred___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredAux), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
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
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_LocalDecl_value_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_17; 
lean_free_object(x_12);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_17;
x_7 = x_15;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = l_Lean_LocalDecl_value_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_2 = x_23;
x_7 = x_20;
goto _start;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_2 = x_37;
x_7 = x_36;
goto _start;
}
}
case 4:
{
lean_object* x_39; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_Expr_isAppOf(x_41, x_1);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_44 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_41, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_2 = x_51;
x_7 = x_50;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = l_Lean_Expr_isAppOf(x_57, x_1);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_57);
x_60 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_57, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_2 = x_66;
x_7 = x_65;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_70 = x_60;
} else {
 lean_dec_ref(x_60);
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
lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_58);
return x_72;
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
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
case 5:
{
lean_object* x_77; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_77 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = l_Lean_Expr_isAppOf(x_79, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_79);
x_82 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_79, x_3, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
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
lean_ctor_set(x_82, 0, x_79);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
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
else
{
uint8_t x_91; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_82);
if (x_91 == 0)
{
return x_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_82, 0);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_82);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = l_Lean_Expr_isAppOf(x_95, x_1);
if (x_97 == 0)
{
lean_object* x_98; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_95);
x_98 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_95, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_95);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_2 = x_104;
x_7 = x_103;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_77);
if (x_111 == 0)
{
return x_77;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_77, 0);
x_113 = lean_ctor_get(x_77, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_77);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
case 8:
{
lean_object* x_115; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Lean_Expr_isAppOf(x_117, x_1);
if (x_119 == 0)
{
lean_object* x_120; 
lean_free_object(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_117);
x_120 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_117, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
lean_ctor_set(x_120, 0, x_117);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_2 = x_127;
x_7 = x_126;
goto _start;
}
}
else
{
uint8_t x_129; 
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_120);
if (x_129 == 0)
{
return x_120;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_115;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_115, 0);
x_134 = lean_ctor_get(x_115, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_115);
x_135 = l_Lean_Expr_isAppOf(x_133, x_1);
if (x_135 == 0)
{
lean_object* x_136; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_133);
x_136 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_133, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
x_2 = x_142;
x_7 = x_141;
goto _start;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_146 = x_136;
} else {
 lean_dec_ref(x_136);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_133);
lean_ctor_set(x_148, 1, x_134);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_115);
if (x_149 == 0)
{
return x_115;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_115, 0);
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_115);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 10:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
lean_dec(x_2);
x_2 = x_153;
goto _start;
}
case 11:
{
lean_object* x_155; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = l_Lean_Expr_isAppOf(x_157, x_1);
if (x_159 == 0)
{
lean_object* x_160; 
lean_free_object(x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_157);
x_160 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_157, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_160);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_160, 0);
lean_dec(x_163);
lean_ctor_set(x_160, 0, x_157);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_157);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_2 = x_167;
x_7 = x_166;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_157);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = !lean_is_exclusive(x_160);
if (x_169 == 0)
{
return x_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_160, 0);
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_160);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_155;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_155, 0);
x_174 = lean_ctor_get(x_155, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_155);
x_175 = l_Lean_Expr_isAppOf(x_173, x_1);
if (x_175 == 0)
{
lean_object* x_176; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_173);
x_176 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_173, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
lean_dec(x_177);
x_2 = x_182;
x_7 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_176, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_176, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_186 = x_176;
} else {
 lean_dec_ref(x_176);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_173);
lean_ctor_set(x_188, 1, x_174);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = !lean_is_exclusive(x_155);
if (x_189 == 0)
{
return x_155;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_155, 0);
x_191 = lean_ctor_get(x_155, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_155);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 12:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
x_193 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_194 = l_unreachable_x21___rarg(x_193);
x_195 = lean_apply_5(x_194, x_3, x_4, x_5, x_6, x_7);
return x_195;
}
default: 
{
lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_7);
return x_196;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_whnfUntil___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1___boxed), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_whnfUntil___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
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
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_whnfUntil___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_whnfUntil___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___at_Lean_Meta_whnfUntil___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_24; lean_object* x_25; 
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_25 = lean_box(x_24);
switch (lean_obj_tag(x_25)) {
case 2:
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(5u);
x_9 = x_26;
goto block_23;
}
case 3:
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(4u);
x_9 = x_27;
goto block_23;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
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
}
block_23:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_WHNF_getStuckMVar_x3f___main___at_Lean_Meta_getStuckMVar_x3f___spec__1(x_16, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
lean_object* l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_WHNF_getStuckMVar_x3f___main___at_Lean_Meta_getStuckMVar_x3f___spec__1(x_17, x_4, x_5, x_6, x_7, x_18);
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
lean_object* l_Lean_WHNF_getStuckMVar_x3f___main___at_Lean_Meta_getStuckMVar_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Expr_getAppFn___main(x_10);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Meta_getConst_x3f(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
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
x_29 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_31, x_33);
x_35 = l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2(x_27, x_16, x_34, x_2, x_3, x_4, x_5, x_26);
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
x_39 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_38);
x_40 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_41, x_43);
x_45 = l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3(x_37, x_16, x_44, x_2, x_3, x_4, x_5, x_36);
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
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
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
}
case 10:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_dec(x_1);
x_1 = x_58;
goto _start;
}
case 11:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_60, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_1 = x_62;
x_6 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
default: 
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_6);
return x_70;
}
}
}
}
lean_object* l_Lean_Meta_getStuckMVar_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_WHNF_getStuckMVar_x3f___main___at_Lean_Meta_getStuckMVar_x3f___spec__1), 6, 1);
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
lean_object* l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_isQuotRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_isRecStuck_x3f___at_Lean_Meta_getStuckMVar_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_Util_WHNF(lean_object*);
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
res = initialize_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1 = _init_l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1();
lean_mark_persistent(l___private_Lean_Util_WHNF_4__toCtorWhenK___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__10___closed__1);
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
l_Lean_Meta_reduceBinNatOp___closed__12 = _init_l_Lean_Meta_reduceBinNatOp___closed__12();
lean_mark_persistent(l_Lean_Meta_reduceBinNatOp___closed__12);
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
l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1 = _init_l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1();
lean_mark_persistent(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1);
l_Lean_Meta_setWHNFRef___closed__1 = _init_l_Lean_Meta_setWHNFRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setWHNFRef___closed__1);
res = l_Lean_Meta_setWHNFRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_whnfHeadPredAux___main___closed__1 = _init_l_Lean_Meta_whnfHeadPredAux___main___closed__1();
lean_mark_persistent(l_Lean_Meta_whnfHeadPredAux___main___closed__1);
l_Lean_Meta_whnfHeadPredAux___main___closed__2 = _init_l_Lean_Meta_whnfHeadPredAux___main___closed__2();
lean_mark_persistent(l_Lean_Meta_whnfHeadPredAux___main___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
