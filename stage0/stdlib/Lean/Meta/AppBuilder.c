// Lean compiler output
// Module: Lean.Meta.AppBuilder
// Imports: Init Lean.Structure Lean.Util.Recognizers Lean.Meta.SynthInstance Lean.Meta.Check
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
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4;
lean_object* l_Lean_Meta_mkLe___rarg___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1;
extern lean_object* l_Lean_getStructureCtor___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_4__mkHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Meta_mkSorry___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7;
lean_object* l_Lean_Meta_mkProjection___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7;
lean_object* l_Lean_Meta_mkEqRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Array_hasQuote___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_7__infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1;
lean_object* l_Lean_Meta_mkCongrFun(lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2;
lean_object* l_Lean_Meta_mkEqMPR___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___closed__2;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4;
lean_object* l_Lean_Meta_mkHEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_15__quoteList___main___rarg___closed__7;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4;
lean_object* l_Lean_Meta_mkEqOfHEq___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3;
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEqNDRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6;
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Meta_mkDecideProof___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5;
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8;
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6;
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__1;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Meta_mkEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_17__mkCongrImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1;
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_5__inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4;
lean_object* l_Lean_Meta_mkAppM___rarg___closed__1;
lean_object* l_Lean_Meta_mkArrayLit(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkDecIsTrue___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_15__quoteList___main___rarg___closed__4;
lean_object* l_Lean_Meta_mkEqMP___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3;
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__2;
lean_object* l_Lean_Meta_mkEqRefl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2;
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4;
lean_object* l_Lean_Meta_mkAppOptM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__4;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5;
lean_object* l_Lean_Meta_mkId___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7;
uint8_t l_Lean_Expr_isForall(lean_object*);
extern lean_object* l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
lean_object* l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5;
lean_object* l_Lean_Meta_mkAppM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Meta_mkDecideProof___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__6;
lean_object* l_Lean_Meta_mkSorry___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm(lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5;
lean_object* l_Lean_Meta_mkLt___rarg___closed__2;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___at_Lean_Meta_mkDecideProof___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7;
lean_object* l_Lean_Meta_mkPure___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1;
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__5;
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*);
lean_object* l_Lean_Meta_mkListLit___at_Lean_Meta_mkArrayLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1;
lean_object* l_Lean_Meta_mkLe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_synthInstance___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2;
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
lean_object* l_Lean_Meta_mkListLit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__4;
lean_object* l_Lean_Meta_mkAppM___rarg___closed__4;
lean_object* l_Lean_Meta_mkHEq(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5;
lean_object* l_Lean_Meta_mkLe___rarg___closed__3;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_27__mkListLitImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3;
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__1;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10;
lean_object* l_Lean_Meta_mkListLit(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4;
lean_object* l_Lean_Meta_mkLt(lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1;
lean_object* _init_l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_4__getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_16 = l_Lean_mkConst(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_23 = l_Lean_mkConst(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_mkId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_1__mkIdImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkId___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l___private_Lean_Meta_InferType_4__getLevelImp(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_14 = l_Lean_mkConst(x_13, x_12);
x_15 = l_Lean_mkAppB(x_14, x_2, x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_21 = l_Lean_mkConst(x_20, x_19);
x_22 = l_Lean_mkAppB(x_21, x_2, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkExpectedTypeHint___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l___private_Lean_Meta_InferType_4__getLevelImp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Expr_eq_x3f___closed__2;
x_17 = l_Lean_mkConst(x_16, x_15);
x_18 = l_Lean_mkApp3(x_17, x_9, x_1, x_2);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Expr_eq_x3f___closed__2;
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = l_Lean_mkApp3(x_24, x_9, x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_mkEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_3__mkEqImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_4__mkHEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_2);
x_11 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l___private_Lean_Meta_InferType_4__getLevelImp(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Expr_heq_x3f___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkApp4(x_20, x_9, x_1, x_12, x_2);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Expr_heq_x3f___closed__2;
x_27 = l_Lean_mkConst(x_26, x_25);
x_28 = l_Lean_mkApp4(x_27, x_9, x_1, x_12, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
lean_dec(x_2);
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
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Meta_mkHEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_4__mkHEqImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkHEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkHEq___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_4__getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_16 = l_Lean_mkConst(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_23 = l_Lean_mkConst(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_mkEqRefl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_5__mkEqReflImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkEqRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqRefl___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_4__getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
x_16 = l_Lean_mkConst(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
x_23 = l_Lean_mkConst(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_mkHEqRefl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkHEqRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkHEqRefl___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_7__infer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_indentExpr(x_1);
x_4 = l_Lean_MessageData_ofList___closed__3;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_KernelException_toMessageData___closed__12;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_indentExpr(x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("AppBuilder for '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symm");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_eq_x3f___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_10);
x_16 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2;
x_19 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Expr_appFn_x21(x_10);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_24 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_22);
x_25 = l___private_Lean_Meta_InferType_4__getLevelImp(x_22, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2;
x_31 = l_Lean_mkConst(x_30, x_29);
x_32 = l_Lean_mkApp4(x_31, x_22, x_23, x_24, x_1);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2;
x_38 = l_Lean_mkConst(x_37, x_36);
x_39 = l_Lean_mkApp4(x_38, x_22, x_23, x_24, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
}
lean_object* l_Lean_Meta_mkEqSymm___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkEqSymm(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqSymm___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trans");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_7__infer(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_52 = l_Lean_Expr_eq_x3f___closed__2;
x_53 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Expr_isAppOfArity___main(x_12, x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_2);
x_55 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_56 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
x_59 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_58, x_57, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
else
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = l_Lean_Expr_isAppOfArity___main(x_15, x_52, x_53);
x_61 = l_Lean_Expr_appFn_x21(x_12);
x_62 = l_Lean_Expr_appFn_x21(x_61);
x_63 = l_Lean_Expr_appArg_x21(x_62);
lean_dec(x_62);
x_64 = l_Lean_Expr_appArg_x21(x_61);
lean_dec(x_61);
x_65 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
if (x_60 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_17 = x_68;
x_18 = x_67;
goto block_51;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Lean_Expr_appFn_x21(x_15);
x_70 = l_Lean_Expr_appFn_x21(x_69);
x_71 = l_Lean_Expr_appArg_x21(x_70);
lean_dec(x_70);
x_72 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_73 = l_Lean_Expr_appArg_x21(x_15);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_17 = x_76;
x_18 = x_67;
goto block_51;
}
}
block_51:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_2, x_15);
x_21 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
x_24 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_23, x_22, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_inc(x_27);
x_31 = l___private_Lean_Meta_InferType_4__getLevelImp(x_27, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
x_37 = l_Lean_mkConst(x_36, x_35);
x_38 = l_Lean_mkApp6(x_37, x_27, x_28, x_29, x_30, x_1, x_2);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
x_44 = l_Lean_mkConst(x_43, x_42);
x_45 = l_Lean_mkApp6(x_44, x_27, x_28, x_29, x_30, x_1, x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
return x_14;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_14, 0);
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_14);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_11);
if (x_81 == 0)
{
return x_11;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_11, 0);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_11);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_7);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
}
}
lean_object* l_Lean_Meta_mkEqTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_11__mkEqTransImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqTrans___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality proof expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_heq_x3f___closed__2;
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_10);
x_16 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1;
x_19 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Expr_appFn_x21(x_10);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_26 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_23);
x_27 = l___private_Lean_Meta_InferType_4__getLevelImp(x_23, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1;
x_33 = l_Lean_mkConst(x_32, x_31);
x_34 = l_Lean_mkApp5(x_33, x_23, x_25, x_24, x_26, x_1);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1;
x_40 = l_Lean_mkConst(x_39, x_38);
x_41 = l_Lean_mkApp5(x_40, x_23, x_25, x_24, x_26, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
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
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
}
lean_object* l_Lean_Meta_mkHEqSymm___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkHEqSymm(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkHEqSymm___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_7__infer(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_56 = l_Lean_Expr_heq_x3f___closed__2;
x_57 = lean_unsigned_to_nat(4u);
x_58 = l_Lean_Expr_isAppOfArity___main(x_12, x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_2);
x_59 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_60 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_63 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_62, x_61, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_63;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = l_Lean_Expr_isAppOfArity___main(x_15, x_56, x_57);
x_65 = l_Lean_Expr_appFn_x21(x_12);
x_66 = l_Lean_Expr_appFn_x21(x_65);
x_67 = l_Lean_Expr_appFn_x21(x_66);
x_68 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_66);
lean_dec(x_66);
x_70 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_71 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
if (x_64 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_17 = x_75;
x_18 = x_74;
goto block_55;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = l_Lean_Expr_appFn_x21(x_15);
x_77 = l_Lean_Expr_appFn_x21(x_76);
x_78 = l_Lean_Expr_appFn_x21(x_77);
x_79 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_80 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
x_81 = l_Lean_Expr_appArg_x21(x_76);
lean_dec(x_76);
x_82 = l_Lean_Expr_appArg_x21(x_15);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_17 = x_86;
x_18 = x_74;
goto block_55;
}
}
block_55:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_2, x_15);
x_22 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_25 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_24, x_23, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_29);
x_35 = l___private_Lean_Meta_InferType_4__getLevelImp(x_29, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_41 = l_Lean_mkConst(x_40, x_39);
x_42 = l_Lean_mkApp8(x_41, x_29, x_31, x_33, x_30, x_32, x_34, x_1, x_2);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_48 = l_Lean_mkConst(x_47, x_46);
x_49 = l_Lean_mkApp8(x_48, x_29, x_31, x_33, x_30, x_32, x_34, x_1, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
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
uint8_t x_87; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_14);
if (x_87 == 0)
{
return x_14;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_14, 0);
x_89 = lean_ctor_get(x_14, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_14);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_11);
if (x_91 == 0)
{
return x_11;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_11, 0);
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_11);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_7);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
}
}
lean_object* l_Lean_Meta_mkHEqTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkHEqTrans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkHEqTrans___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eqOfHEq");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality types are not definitionally equal");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("is not definitionally equal to");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_heq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_13 = l_Lean_indentExpr(x_1);
x_14 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_17 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_16, x_15, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = l_Lean_Expr_appFn_x21(x_8);
x_19 = l_Lean_Expr_appFn_x21(x_18);
x_20 = l_Lean_Expr_appFn_x21(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_23 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_24 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
lean_inc(x_21);
x_25 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_21, x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_indentExpr(x_21);
x_30 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_MessageData_ofList___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_indentExpr(x_23);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_39 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_38, x_37, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
lean_inc(x_21);
x_45 = l___private_Lean_Meta_InferType_4__getLevelImp(x_21, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_51 = l_Lean_mkConst(x_50, x_49);
x_52 = l_Lean_mkApp4(x_51, x_21, x_22, x_24, x_1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_58 = l_Lean_mkConst(x_57, x_56);
x_59 = l_Lean_mkApp4(x_58, x_21, x_22, x_24, x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
return x_45;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l_Lean_Meta_mkEqOfHEq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqOfHEq___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrArg");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non-dependent function expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Lean_Meta_AppBuilder_7__infer(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_57; lean_object* x_66; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_91 = l_Lean_Expr_eq_x3f___closed__2;
x_92 = lean_unsigned_to_nat(3u);
x_93 = l_Lean_Expr_isAppOfArity___main(x_9, x_91, x_92);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_12, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_12, 2);
lean_inc(x_95);
x_96 = l_Lean_Expr_hasLooseBVars(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (x_93 == 0)
{
x_57 = x_98;
goto block_65;
}
else
{
x_66 = x_98;
goto block_90;
}
}
else
{
lean_object* x_99; 
lean_dec(x_95);
lean_dec(x_94);
x_99 = lean_box(0);
if (x_93 == 0)
{
x_57 = x_99;
goto block_65;
}
else
{
x_66 = x_99;
goto block_90;
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
if (x_93 == 0)
{
x_57 = x_100;
goto block_65;
}
else
{
x_66 = x_100;
goto block_90;
}
}
block_56:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_2, x_9);
x_17 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
x_20 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_19, x_18, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_23);
x_27 = l___private_Lean_Meta_InferType_4__getLevelImp(x_23, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_24);
x_30 = l___private_Lean_Meta_InferType_4__getLevelImp(x_24, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
x_37 = l_Lean_mkConst(x_36, x_35);
x_38 = l_Lean_mkApp6(x_37, x_23, x_24, x_25, x_26, x_1, x_2);
lean_ctor_set(x_30, 0, x_38);
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
x_45 = l_Lean_mkConst(x_44, x_43);
x_46 = l_Lean_mkApp6(x_45, x_23, x_24, x_25, x_26, x_1, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_65:
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_2);
x_58 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_59 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
x_62 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_61, x_60, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_box(0);
x_14 = x_64;
x_15 = x_63;
goto block_56;
}
}
block_90:
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_9);
lean_dec(x_2);
x_67 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_68 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2;
x_71 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_70, x_69, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_12);
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = l_Lean_Expr_appFn_x21(x_9);
x_75 = l_Lean_Expr_appFn_x21(x_74);
x_76 = l_Lean_Expr_appArg_x21(x_75);
lean_dec(x_75);
x_77 = l_Lean_Expr_appArg_x21(x_74);
lean_dec(x_74);
x_78 = l_Lean_Expr_appArg_x21(x_9);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_66, 0, x_80);
x_14 = x_66;
x_15 = x_73;
goto block_56;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_66, 0);
lean_inc(x_81);
lean_dec(x_66);
x_82 = l_Lean_Expr_appFn_x21(x_9);
x_83 = l_Lean_Expr_appFn_x21(x_82);
x_84 = l_Lean_Expr_appArg_x21(x_83);
lean_dec(x_83);
x_85 = l_Lean_Expr_appArg_x21(x_82);
lean_dec(x_82);
x_86 = l_Lean_Expr_appArg_x21(x_9);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_14 = x_89;
x_15 = x_81;
goto block_56;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_11);
if (x_101 == 0)
{
return x_11;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_11, 0);
x_103 = lean_ctor_get(x_11, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Meta_mkCongrArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkCongrArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrArg___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof between functions expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_eq_x3f___closed__2;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_9);
x_15 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
x_18 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_17, x_16, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = l_Lean_Expr_appFn_x21(x_9);
x_20 = l_Lean_Expr_appFn_x21(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_23 = l_Lean_Expr_appArg_x21(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_21, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_25, 2);
lean_inc(x_36);
lean_dec(x_25);
x_37 = 0;
lean_inc(x_35);
x_38 = l_Lean_mkLambda(x_34, x_37, x_35, x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_39 = l___private_Lean_Meta_InferType_4__getLevelImp(x_35, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_2);
lean_inc(x_38);
x_42 = l_Lean_mkApp(x_38, x_2);
x_43 = l___private_Lean_Meta_InferType_4__getLevelImp(x_42, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
x_50 = l_Lean_mkConst(x_49, x_48);
x_51 = l_Lean_mkApp6(x_50, x_35, x_38, x_22, x_23, x_1, x_2);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
x_58 = l_Lean_mkConst(x_57, x_56);
x_59 = l_Lean_mkApp6(x_58, x_35, x_38, x_22, x_23, x_1, x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_43);
if (x_61 == 0)
{
return x_43;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_43, 0);
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_43);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_69 = lean_box(0);
x_27 = x_69;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
x_28 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_9);
x_29 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
x_32 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_31, x_30, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
}
else
{
uint8_t x_70; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_24);
if (x_70 == 0)
{
return x_24;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_24, 0);
x_72 = lean_ctor_get(x_24, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_24);
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
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_8);
if (x_74 == 0)
{
return x_8;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_8, 0);
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_8);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
lean_object* l_Lean_Meta_mkCongrFun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkCongrFun(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrFun___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congr");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_17__mkCongrImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_2);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_78 = l_Lean_Expr_eq_x3f___closed__2;
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Expr_isAppOfArity___main(x_9, x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_2);
x_81 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_9);
x_82 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
x_85 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_84, x_83, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_85;
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = l_Lean_Expr_isAppOfArity___main(x_12, x_78, x_79);
x_87 = l_Lean_Expr_appFn_x21(x_9);
x_88 = l_Lean_Expr_appFn_x21(x_87);
x_89 = l_Lean_Expr_appArg_x21(x_88);
lean_dec(x_88);
x_90 = l_Lean_Expr_appArg_x21(x_87);
lean_dec(x_87);
x_91 = l_Lean_Expr_appArg_x21(x_9);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
if (x_86 == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_14 = x_94;
x_15 = x_93;
goto block_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = l_Lean_Expr_appFn_x21(x_12);
x_96 = l_Lean_Expr_appFn_x21(x_95);
x_97 = l_Lean_Expr_appArg_x21(x_96);
lean_dec(x_96);
x_98 = l_Lean_Expr_appArg_x21(x_95);
lean_dec(x_95);
x_99 = l_Lean_Expr_appArg_x21(x_12);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_14 = x_102;
x_15 = x_93;
goto block_77;
}
}
block_77:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_2, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_24, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 2);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lean_Expr_hasLooseBVars(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_27);
x_42 = l___private_Lean_Meta_InferType_4__getLevelImp(x_27, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_40);
x_45 = l___private_Lean_Meta_InferType_4__getLevelImp(x_40, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
x_52 = l_Lean_mkConst(x_51, x_50);
x_53 = l_Lean_mkApp8(x_52, x_27, x_40, x_25, x_26, x_28, x_29, x_1, x_2);
lean_ctor_set(x_45, 0, x_53);
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
x_60 = l_Lean_mkConst(x_59, x_58);
x_61 = l_Lean_mkApp8(x_60, x_27, x_40, x_25, x_26, x_28, x_29, x_1, x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_45);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_42);
if (x_67 == 0)
{
return x_42;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
x_71 = lean_box(0);
x_33 = x_71;
goto block_39;
}
}
else
{
lean_object* x_72; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
x_72 = lean_box(0);
x_33 = x_72;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
x_34 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_9);
x_35 = l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2;
x_38 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_37, x_36, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
}
else
{
uint8_t x_73; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_30);
if (x_73 == 0)
{
return x_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_30, 0);
x_75 = lean_ctor_get(x_30, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_30);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
return x_11;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_11);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Meta_mkCongr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_17__mkCongrImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkCongr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongr___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_synthInstance___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_12);
x_13 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_12, x_18, x_3, x_4, x_5, x_6, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result contains metavariables");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2(x_4, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_10, x_2);
x_14 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_13, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__8(x_15, x_5, x_6, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_indentExpr(x_15);
x_26 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_1, x_27, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_18__mkAppMFinal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppM");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit arguments provided to");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_80; lean_object* x_81; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_47 = lean_array_get_size(x_4);
x_48 = lean_expr_instantiate_rev_range(x_44, x_5, x_47, x_4);
lean_dec(x_47);
lean_dec(x_44);
x_80 = (uint8_t)((x_46 << 24) >> 61);
x_81 = lean_box(x_80);
switch (lean_obj_tag(x_81)) {
case 1:
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_48);
x_83 = 0;
lean_inc(x_8);
x_84 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_82, x_83, x_43, x_8, x_9, x_10, x_11, x_12);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_array_push(x_4, x_85);
x_4 = x_87;
x_7 = x_45;
x_12 = x_86;
goto _start;
}
case 3:
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_48);
x_90 = 1;
lean_inc(x_8);
x_91 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_89, x_90, x_43, x_8, x_9, x_10, x_11, x_12);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_92);
x_94 = lean_array_push(x_4, x_92);
x_95 = l_Lean_Expr_mvarId_x21(x_92);
lean_dec(x_92);
x_96 = lean_array_push(x_6, x_95);
x_4 = x_94;
x_6 = x_96;
x_7 = x_45;
x_12 = x_93;
goto _start;
}
default: 
{
lean_object* x_98; 
lean_dec(x_81);
lean_dec(x_43);
x_98 = lean_box(0);
x_49 = x_98;
goto block_79;
}
}
block_79:
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_49);
x_50 = lean_array_get_size(x_2);
x_51 = lean_nat_dec_lt(x_3, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_3);
x_52 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_53 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_52, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_54);
x_55 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_54, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_58 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_48, x_56, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_62, x_1);
lean_dec(x_4);
x_64 = l_Lean_MessageData_Inhabited___closed__1;
x_65 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_63, x_54, x_64, x_8, x_9, x_10, x_11, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_3, x_67);
lean_dec(x_3);
x_69 = lean_array_push(x_4, x_54);
x_3 = x_68;
x_4 = x_69;
x_7 = x_45;
x_12 = x_66;
goto _start;
}
}
else
{
uint8_t x_71; 
lean_dec(x_54);
lean_dec(x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_58, 0);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_58);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_55);
if (x_75 == 0)
{
return x_55;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_55, 0);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_55);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_99; 
x_99 = lean_box(0);
x_13 = x_99;
goto block_42;
}
block_42:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_4);
x_15 = lean_expr_instantiate_rev_range(x_7, x_5, x_14, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_isForall(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_14);
x_20 = lean_array_get_size(x_2);
x_21 = lean_nat_dec_eq(x_3, x_20);
lean_dec(x_20);
lean_dec(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = l_Lean_indentExpr(x_1);
x_23 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_MessageData_ofList___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
x_31 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_29, x_30);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_34 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_33, x_32, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_36 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_35, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_6);
lean_dec(x_4);
return x_36;
}
}
else
{
x_5 = x_14;
x_7 = x_17;
x_12 = x_18;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_13);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(x_21, x_2, x_3, x_4, x_5, x_24);
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
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
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
}
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_lparams(x_8);
x_11 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Lean_mkConst(x_1, x_13);
x_15 = lean_instantiate_type_lparams(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_17);
x_19 = l_Lean_mkConst(x_1, x_17);
x_20 = lean_instantiate_type_lparams(x_8, x_17);
lean_dec(x_17);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_8, x_1, x_10, x_11, x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 2);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_21);
x_22 = lean_st_ref_set(x_7, x_15, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_7);
x_24 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_7, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_7, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 2);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_13);
x_36 = lean_st_ref_set(x_7, x_30, x_32);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_13);
lean_ctor_set(x_30, 2, x_42);
x_43 = lean_st_ref_set(x_7, x_30, x_32);
lean_dec(x_7);
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
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_13);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_st_ref_set(x_7, x_52, x_32);
lean_dec(x_7);
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
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_57 = lean_ctor_get(x_24, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_st_ref_get(x_7, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_7, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 2);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_13);
x_68 = lean_st_ref_set(x_7, x_62, x_64);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 0, x_57);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
lean_dec(x_63);
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_13);
lean_ctor_set(x_62, 2, x_74);
x_75 = lean_st_ref_set(x_7, x_62, x_64);
lean_dec(x_7);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_57);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_62, 0);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_62);
x_81 = lean_ctor_get(x_63, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_82 = x_63;
} else {
 lean_dec_ref(x_63);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 1, 1);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_13);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_st_ref_set(x_7, x_84, x_64);
lean_dec(x_7);
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
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_57);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_16, 0);
lean_inc(x_89);
lean_dec(x_16);
x_90 = 0;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
lean_ctor_set(x_15, 2, x_91);
x_92 = lean_st_ref_set(x_7, x_15, x_17);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_7);
x_94 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_7, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_take(x_7, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 1, 1);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_104);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_st_ref_set(x_7, x_109, x_102);
lean_dec(x_7);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_94, 1);
lean_inc(x_115);
lean_dec(x_94);
x_116 = lean_st_ref_get(x_7, x_115);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_st_ref_take(x_7, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 1, 1);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_123);
lean_ctor_set(x_128, 2, x_127);
x_129 = lean_st_ref_set(x_7, x_128, x_121);
lean_dec(x_7);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_114);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_133 = lean_ctor_get(x_15, 0);
x_134 = lean_ctor_get(x_15, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_15);
x_135 = lean_ctor_get(x_16, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_136 = x_16;
} else {
 lean_dec_ref(x_16);
 x_136 = lean_box(0);
}
x_137 = 0;
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_137);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_st_ref_set(x_7, x_139, x_17);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
lean_inc(x_7);
x_142 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_7, x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_st_ref_take(x_7, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 x_153 = x_148;
} else {
 lean_dec_ref(x_148);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 3, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_152);
lean_ctor_set(x_157, 2, x_156);
x_158 = lean_st_ref_set(x_7, x_157, x_150);
lean_dec(x_7);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_143);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_162 = lean_ctor_get(x_142, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_142, 1);
lean_inc(x_163);
lean_dec(x_142);
x_164 = lean_st_ref_get(x_7, x_163);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_st_ref_take(x_7, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_167, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_168, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 1, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_172)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_172;
}
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_171);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_st_ref_set(x_7, x_176, x_169);
lean_dec(x_7);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
 lean_ctor_set_tag(x_180, 1);
}
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_7, x_8);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_184 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_182, x_2, x_4, x_5, x_6, x_7, x_186);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 0);
lean_dec(x_189);
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
lean_dec(x_184);
x_194 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_182, x_2, x_4, x_5, x_6, x_7, x_193);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 0);
lean_dec(x_196);
lean_ctor_set_tag(x_194, 1);
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appBuilder");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_mkAppM___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_mkAppM___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_20__mkFun___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__2___boxed), 8, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAppM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkAppM___rarg___lambda__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_array_push(x_4, x_11);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppOptM");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments provided to");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_49 = lean_array_get_size(x_4);
x_50 = lean_expr_instantiate_rev_range(x_46, x_5, x_49, x_4);
lean_dec(x_49);
lean_dec(x_46);
x_51 = lean_array_get_size(x_2);
x_52 = lean_nat_dec_lt(x_3, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_3);
x_53 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_54 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_53, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; lean_object* x_57; 
x_56 = (uint8_t)((x_48 << 24) >> 61);
x_57 = lean_box(x_56);
if (lean_obj_tag(x_57) == 3)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_50);
x_59 = 1;
lean_inc(x_8);
x_60 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_58, x_59, x_45, x_8, x_9, x_10, x_11, x_12);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_3, x_63);
lean_dec(x_3);
lean_inc(x_61);
x_65 = lean_array_push(x_4, x_61);
x_66 = l_Lean_Expr_mvarId_x21(x_61);
lean_dec(x_61);
x_67 = lean_array_push(x_6, x_66);
x_3 = x_64;
x_4 = x_65;
x_6 = x_67;
x_7 = x_47;
x_12 = x_62;
goto _start;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_57);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_50);
x_70 = 0;
lean_inc(x_8);
x_71 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_69, x_70, x_45, x_8, x_9, x_10, x_11, x_12);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_3, x_74);
lean_dec(x_3);
x_76 = lean_array_push(x_4, x_72);
x_3 = x_75;
x_4 = x_76;
x_7 = x_47;
x_12 = x_73;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_45);
x_78 = lean_ctor_get(x_55, 0);
lean_inc(x_78);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_78);
x_79 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_78, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_82 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_50, x_80, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_86, x_1);
lean_dec(x_4);
x_88 = l_Lean_MessageData_Inhabited___closed__1;
x_89 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_87, x_78, x_88, x_8, x_9, x_10, x_11, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_dec(x_82);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_3, x_91);
lean_dec(x_3);
x_93 = lean_array_push(x_4, x_78);
x_3 = x_92;
x_4 = x_93;
x_7 = x_47;
x_12 = x_90;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_78);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
return x_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_82);
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
lean_dec(x_78);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_79);
if (x_99 == 0)
{
return x_79;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_79, 0);
x_101 = lean_ctor_get(x_79, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_79);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_13 = x_103;
goto block_44;
}
block_44:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_4);
x_15 = lean_expr_instantiate_rev_range(x_7, x_5, x_14, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_isForall(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_14);
x_20 = lean_array_get_size(x_2);
x_21 = lean_nat_dec_eq(x_3, x_20);
lean_dec(x_20);
lean_dec(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_empty___closed__1;
x_24 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1(x_2, x_2, x_22, x_23);
x_25 = l_Lean_indentExpr(x_1);
x_26 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_MessageData_ofList___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_hasCoeOfArrayExpr___closed__2;
x_33 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_24, x_22, x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_36 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_35, x_34, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_38 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_37, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_6);
lean_dec(x_4);
return x_38;
}
}
else
{
x_5 = x_14;
x_7 = x_17;
x_12 = x_18;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_8, x_1, x_10, x_11, x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAppOptM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_20__mkFun___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__2___boxed), 8, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAppOptM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppOptM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrec");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid motive");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_3, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_27 = l___private_Lean_Meta_InferType_4__getLevelImp(x_24, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
if (lean_obj_tag(x_32) == 7)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_32, 2);
lean_inc(x_41);
lean_dec(x_32);
if (lean_obj_tag(x_41) == 3)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_47 = l_Lean_mkConst(x_46, x_45);
x_48 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_49 = lean_array_push(x_48, x_24);
x_50 = lean_array_push(x_49, x_25);
x_51 = lean_array_push(x_50, x_1);
x_52 = lean_array_push(x_51, x_2);
x_53 = lean_array_push(x_52, x_26);
x_54 = lean_array_push(x_53, x_3);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_54, x_54, x_55, x_47);
lean_dec(x_54);
lean_ctor_set(x_30, 0, x_56);
return x_30;
}
else
{
lean_object* x_57; 
lean_dec(x_41);
lean_free_object(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_34 = x_57;
goto block_40;
}
}
else
{
lean_object* x_58; 
lean_free_object(x_30);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(0);
x_34 = x_58;
goto block_40;
}
block_40:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_35 = l_Lean_indentExpr(x_1);
x_36 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_39 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_38, x_37, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
if (lean_obj_tag(x_59) == 7)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_59, 2);
lean_inc(x_68);
lean_dec(x_59);
if (lean_obj_tag(x_68) == 3)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_28);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_74 = l_Lean_mkConst(x_73, x_72);
x_75 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_76 = lean_array_push(x_75, x_24);
x_77 = lean_array_push(x_76, x_25);
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_2);
x_80 = lean_array_push(x_79, x_26);
x_81 = lean_array_push(x_80, x_3);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_81, x_81, x_82, x_74);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_60);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_68);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_box(0);
x_61 = x_85;
goto block_67;
}
}
else
{
lean_object* x_86; 
lean_dec(x_59);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
x_61 = x_86;
goto block_67;
}
block_67:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
x_62 = l_Lean_indentExpr(x_1);
x_63 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_66 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_65, x_64, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_66;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_30);
if (x_87 == 0)
{
return x_30;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_30, 0);
x_89 = lean_ctor_get(x_30, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_30);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_27);
if (x_91 == 0)
{
return x_27;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_27, 0);
x_93 = lean_ctor_get(x_27, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_27);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_11);
if (x_95 == 0)
{
return x_11;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_11, 0);
x_97 = lean_ctor_get(x_11, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_11);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_8);
return x_99;
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp), 8, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_mkEqNDRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqNDRec___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_mkRecFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_7__infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_indentExpr(x_3);
x_18 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_21 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_27 = l___private_Lean_Meta_InferType_4__getLevelImp(x_24, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
if (lean_obj_tag(x_32) == 7)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_32, 2);
lean_inc(x_41);
lean_dec(x_32);
if (lean_obj_tag(x_41) == 7)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 3)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_48 = l_Lean_mkConst(x_47, x_46);
x_49 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_50 = lean_array_push(x_49, x_24);
x_51 = lean_array_push(x_50, x_25);
x_52 = lean_array_push(x_51, x_1);
x_53 = lean_array_push(x_52, x_2);
x_54 = lean_array_push(x_53, x_26);
x_55 = lean_array_push(x_54, x_3);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_55, x_55, x_56, x_48);
lean_dec(x_55);
lean_ctor_set(x_30, 0, x_57);
return x_30;
}
else
{
lean_object* x_58; 
lean_dec(x_42);
lean_free_object(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(0);
x_34 = x_58;
goto block_40;
}
}
else
{
lean_object* x_59; 
lean_dec(x_41);
lean_free_object(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_34 = x_59;
goto block_40;
}
}
else
{
lean_object* x_60; 
lean_free_object(x_30);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
x_34 = x_60;
goto block_40;
}
block_40:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_35 = l_Lean_indentExpr(x_1);
x_36 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_39 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_38, x_37, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
if (lean_obj_tag(x_61) == 7)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_61, 2);
lean_inc(x_70);
lean_dec(x_61);
if (lean_obj_tag(x_70) == 7)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 3)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_28);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_77 = l_Lean_mkConst(x_76, x_75);
x_78 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_79 = lean_array_push(x_78, x_24);
x_80 = lean_array_push(x_79, x_25);
x_81 = lean_array_push(x_80, x_1);
x_82 = lean_array_push(x_81, x_2);
x_83 = lean_array_push(x_82, x_26);
x_84 = lean_array_push(x_83, x_3);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_84, x_84, x_85, x_77);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_62);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_71);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(0);
x_63 = x_88;
goto block_69;
}
}
else
{
lean_object* x_89; 
lean_dec(x_70);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_box(0);
x_63 = x_89;
goto block_69;
}
}
else
{
lean_object* x_90; 
lean_dec(x_61);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_box(0);
x_63 = x_90;
goto block_69;
}
block_69:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_64 = l_Lean_indentExpr(x_1);
x_65 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_68 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_67, x_66, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_68;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_30);
if (x_91 == 0)
{
return x_30;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_30, 0);
x_93 = lean_ctor_get(x_30, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_30);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_27);
if (x_95 == 0)
{
return x_27;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_27, 0);
x_97 = lean_ctor_get(x_27, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_27);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
return x_11;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_11, 0);
x_101 = lean_ctor_get(x_11, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_11);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_2);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
}
}
lean_object* l_Lean_Meta_mkEqRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_23__mkEqRecImp), 8, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_mkEqRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqRec___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqMP___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mp");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqMP___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqMP___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqMP___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_mkAppStx___closed__9;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_array_push(x_5, x_3);
x_7 = l_Lean_Meta_mkEqMP___rarg___closed__2;
x_8 = l_Lean_Meta_mkAppM___rarg(x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkEqMP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqMP___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqMPR___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mpr");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqMPR___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqMPR___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqMPR___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_mkAppStx___closed__9;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_array_push(x_5, x_3);
x_7 = l_Lean_Meta_mkEqMPR___rarg___closed__2;
x_8 = l_Lean_Meta_mkAppM___rarg(x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkEqMPR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqMPR___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noConfusion");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive type expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_2, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_24, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn___main(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_6, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_environment_find(x_36, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_indentExpr(x_28);
x_39 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_42 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_41, x_40, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
if (lean_obj_tag(x_43) == 5)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_45 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
x_51 = lean_name_mk_string(x_49, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_32);
x_53 = l_Lean_mkConst(x_51, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_54);
x_56 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = l___private_Lean_Expr_3__getAppArgsAux___main(x_28, x_57, x_59);
x_61 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_62 = lean_array_push(x_61, x_1);
x_63 = lean_array_push(x_62, x_25);
x_64 = lean_array_push(x_63, x_26);
x_65 = lean_array_push(x_64, x_2);
x_66 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_65, x_65, x_54, x_60);
lean_dec(x_65);
x_67 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_66, x_66, x_54, x_53);
lean_dec(x_66);
lean_ctor_set(x_45, 0, x_67);
return x_45;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_70 = lean_ctor_get(x_44, 0);
lean_inc(x_70);
lean_dec(x_44);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
x_73 = lean_name_mk_string(x_71, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_32);
x_75 = l_Lean_mkConst(x_73, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_76);
x_78 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_77);
x_79 = lean_mk_array(x_77, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_77, x_80);
lean_dec(x_77);
x_82 = l___private_Lean_Expr_3__getAppArgsAux___main(x_28, x_79, x_81);
x_83 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_84 = lean_array_push(x_83, x_1);
x_85 = lean_array_push(x_84, x_25);
x_86 = lean_array_push(x_85, x_26);
x_87 = lean_array_push(x_86, x_2);
x_88 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_87, x_87, x_76, x_82);
lean_dec(x_87);
x_89 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_88, x_88, x_76, x_75);
lean_dec(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_69);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_44);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_45);
if (x_91 == 0)
{
return x_45;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_45, 0);
x_93 = lean_ctor_get(x_45, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_45);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_43);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_95 = l_Lean_indentExpr(x_28);
x_96 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_99 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_98, x_97, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lean_indentExpr(x_28);
x_101 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_104 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_103, x_102, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_104;
}
}
else
{
uint8_t x_105; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_27);
if (x_105 == 0)
{
return x_27;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_27, 0);
x_107 = lean_ctor_get(x_27, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_27);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_11);
if (x_109 == 0)
{
return x_11;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
return x_8;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_8, 0);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_8);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
lean_object* l_Lean_Meta_mkNoConfusion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkNoConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasPure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPure___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkPure___rarg___closed__2;
x_2 = l_Lean_Meta_mkPure___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkPure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_5);
x_11 = lean_array_push(x_10, x_6);
x_12 = l_Lean_Meta_mkPure___rarg___closed__4;
x_13 = l_Lean_Meta_mkAppOptM___rarg(x_1, x_12, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_mkPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkPure___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_6, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget(x_5, x_6);
lean_inc(x_23);
lean_inc(x_3);
lean_inc(x_4);
x_24 = l_Lean_isSubobjectField_x3f(x_4, x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_23);
x_25 = lean_box(0);
x_12 = x_25;
x_13 = x_11;
goto block_18;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_28 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = lean_st_ref_get(x_10, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_8, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_40 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_29, x_2, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_35);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_ctor_set(x_24, 0, x_41);
x_12 = x_24;
x_13 = x_42;
goto block_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_24);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_35, x_7, x_8, x_9, x_10, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_39, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_12 = x_31;
x_13 = x_47;
goto block_18;
}
}
else
{
uint8_t x_48; 
lean_free_object(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_52; 
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_52 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = lean_st_ref_get(x_10, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_8, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_64 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_53, x_2, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_12 = x_67;
x_13 = x_66;
goto block_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_59, x_7, x_8, x_9, x_10, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_63, x_7, x_8, x_9, x_10, x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_12 = x_55;
x_13 = x_72;
goto block_18;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_52, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_75 = x_52;
} else {
 lean_dec_ref(x_52);
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
block_18:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
x_11 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkProjectionn");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getStructureCtor___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field name '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkProjection");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_21 = l_Lean_Expr_getAppFn___main(x_12);
if (lean_obj_tag(x_21) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_71; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_6, x_13);
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
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_22);
lean_inc(x_28);
x_71 = l_Lean_isStructureLike(x_28, x_22);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_72 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_73 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12;
x_76 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_75, x_74, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
x_29 = x_26;
goto block_70;
}
block_70:
{
lean_object* x_30; 
lean_inc(x_2);
lean_inc(x_22);
lean_inc(x_28);
x_30 = l_Lean_getProjFnForField_x3f(x_28, x_22, x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_23);
lean_inc(x_22);
lean_inc(x_28);
x_31 = l_Lean_getStructureFields(x_28, x_22);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1(x_1, x_2, x_22, x_28, x_31, x_32, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_System_FilePath_dirName___closed__1;
x_37 = l_Lean_Name_toStringWithSep___main(x_36, x_2);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2;
x_47 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_46, x_45, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_50);
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_dec(x_33);
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_33);
if (x_54 == 0)
{
return x_33;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_33, 0);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_33);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
lean_dec(x_30);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Expr_getAppNumArgsAux___main(x_12, x_59);
x_61 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_60);
x_62 = lean_mk_array(x_60, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_60, x_63);
lean_dec(x_60);
x_65 = l___private_Lean_Expr_3__getAppArgsAux___main(x_12, x_62, x_64);
x_66 = l_Lean_mkConst(x_58, x_23);
x_67 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_65, x_65, x_59, x_66);
lean_dec(x_65);
x_68 = l_Lean_mkApp(x_67, x_1);
if (lean_is_scalar(x_27)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_27;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_29);
return x_69;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_21);
lean_dec(x_2);
x_81 = lean_box(0);
x_14 = x_81;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_15 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_16 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2;
x_19 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_18, x_17, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
else
{
uint8_t x_82; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
return x_11;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_11, 0);
x_84 = lean_ctor_get(x_11, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_11);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkProjection___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkProjection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkProjection___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
x_6 = l_Lean_mkApp(x_2, x_4);
x_7 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(x_1, x_2, x_5);
x_8 = l_Lean_mkApp(x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_27__mkListLitImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Init_LeanInit_15__quoteList___main___rarg___closed__4;
lean_inc(x_12);
x_14 = l_Lean_mkConst(x_13, x_12);
lean_inc(x_1);
x_15 = l_Lean_mkApp(x_14, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l___private_Init_LeanInit_15__quoteList___main___rarg___closed__7;
x_17 = l_Lean_mkConst(x_16, x_12);
x_18 = l_Lean_mkApp(x_17, x_1);
x_19 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(x_15, x_18, x_2);
lean_dec(x_15);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Init_LeanInit_15__quoteList___main___rarg___closed__4;
lean_inc(x_23);
x_25 = l_Lean_mkConst(x_24, x_23);
lean_inc(x_1);
x_26 = l_Lean_mkApp(x_25, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l___private_Init_LeanInit_15__quoteList___main___rarg___closed__7;
x_29 = l_Lean_mkConst(x_28, x_23);
x_30 = l_Lean_mkApp(x_29, x_1);
x_31 = l___private_Lean_Meta_AppBuilder_26__mkListLitAux___main(x_26, x_30, x_2);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_mkListLit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_27__mkListLitImp), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkListLit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkListLit___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkListLit___at_Lean_Meta_mkArrayLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_27__mkListLitImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkArrayLit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_27__mkListLitImp(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Array_hasQuote___rarg___closed__2;
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = l_Lean_mkApp(x_15, x_1);
x_17 = l_Lean_mkApp(x_16, x_11);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Array_hasQuote___rarg___closed__2;
x_23 = l_Lean_mkConst(x_22, x_21);
x_24 = l_Lean_mkApp(x_23, x_1);
x_25 = l_Lean_mkApp(x_24, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_mkArrayLit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkArrayLit___rarg___lambda__1), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkArrayLit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkArrayLit___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_boolToExpr___lambda__1___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_boolToExpr___lambda__1___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
x_12 = l_Lean_mkConst(x_11, x_10);
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3;
x_14 = l_Lean_mkAppB(x_12, x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4;
x_17 = l_Lean_mkAppB(x_12, x_2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
lean_object* l_Lean_Meta_mkSorry___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_5__inferForallType___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkSorry___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkSorry___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_mkSorry___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkSorry___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Meta_mkSorry___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_20__mkFun___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_206 = lean_st_ref_get(x_6, x_7);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 2);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get_uint8(x_208, sizeof(void*)*1);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = 0;
x_11 = x_211;
x_12 = x_210;
goto block_205;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_206, 1);
lean_inc(x_212);
lean_dec(x_206);
x_213 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_214 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_213, x_3, x_4, x_5, x_6, x_212);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_unbox(x_215);
lean_dec(x_215);
x_11 = x_217;
x_12 = x_216;
goto block_205;
}
block_205:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_6, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 2);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_25);
x_26 = lean_st_ref_set(x_6, x_19, x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_6);
x_28 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_6, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_take(x_6, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 2);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_17);
x_40 = lean_st_ref_set(x_6, x_34, x_36);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_17);
lean_ctor_set(x_34, 2, x_46);
x_47 = lean_st_ref_set(x_6, x_34, x_36);
lean_dec(x_6);
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
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_54 = x_35;
} else {
 lean_dec_ref(x_35);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_17);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_st_ref_set(x_6, x_56, x_36);
lean_dec(x_6);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_29);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_ctor_get(x_28, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
x_63 = lean_st_ref_get(x_6, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_6, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_66, 2);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_17);
x_72 = lean_st_ref_set(x_6, x_66, x_68);
lean_dec(x_6);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_61);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_dec(x_67);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_17);
lean_ctor_set(x_66, 2, x_78);
x_79 = lean_st_ref_set(x_6, x_66, x_68);
lean_dec(x_6);
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
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_61);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_66, 0);
x_84 = lean_ctor_get(x_66, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_66);
x_85 = lean_ctor_get(x_67, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_86 = x_67;
} else {
 lean_dec_ref(x_67);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 1, 1);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_17);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_st_ref_set(x_6, x_88, x_68);
lean_dec(x_6);
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
lean_ctor_set(x_92, 0, x_61);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
lean_dec(x_20);
x_94 = 0;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
lean_ctor_set(x_19, 2, x_95);
x_96 = lean_st_ref_set(x_6, x_19, x_21);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_6);
x_98 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_get(x_6, x_100);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_st_ref_take(x_6, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 1, 1);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 3, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_108);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_st_ref_set(x_6, x_113, x_106);
lean_dec(x_6);
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
lean_ctor_set(x_117, 0, x_99);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_dec(x_98);
x_120 = lean_st_ref_get(x_6, x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_st_ref_take(x_6, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 1);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_128)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_128;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_st_ref_set(x_6, x_132, x_125);
lean_dec(x_6);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_19, 0);
x_138 = lean_ctor_get(x_19, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_19);
x_139 = lean_ctor_get(x_20, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_140 = x_20;
} else {
 lean_dec_ref(x_20);
 x_140 = lean_box(0);
}
x_141 = 0;
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_st_ref_set(x_6, x_143, x_21);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
lean_inc(x_6);
x_146 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_st_ref_get(x_6, x_148);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_6, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_159 = x_153;
} else {
 lean_dec_ref(x_153);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 1, 1);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_st_ref_set(x_6, x_161, x_154);
lean_dec(x_6);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_147);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_166 = lean_ctor_get(x_146, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_dec(x_146);
x_168 = lean_st_ref_get(x_6, x_167);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_st_ref_take(x_6, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 1, 1);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_176)) {
 x_180 = lean_alloc_ctor(0, 3, 0);
} else {
 x_180 = x_176;
}
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_175);
lean_ctor_set(x_180, 2, x_179);
x_181 = lean_st_ref_set(x_6, x_180, x_173);
lean_dec(x_6);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_166);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_6, x_12);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_188 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_192 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_186, x_191, x_3, x_4, x_5, x_6, x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
lean_ctor_set(x_192, 0, x_189);
return x_192;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_189);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_188, 1);
lean_inc(x_198);
lean_dec(x_188);
x_199 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_200 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_186, x_199, x_3, x_4, x_5, x_6, x_198);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_200, 0);
lean_dec(x_202);
lean_ctor_set_tag(x_200, 1);
lean_ctor_set(x_200, 0, x_197);
return x_200;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
}
}
lean_object* l_Lean_Meta_mkEq___at_Lean_Meta_mkDecideProof___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Meta_mkDecideProof___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Meta_mkDecideProof___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofDecideEqTrue");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_boolToExpr___lambda__1___closed__6;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_8, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(x_13, x_10, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_1, x_16);
x_19 = l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
x_20 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_19, x_18, x_3, x_4, x_5, x_6, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decide");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_Meta_mkDecideProof___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkDecideProof___rarg___lambda__1), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkDecideProof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_mkOptionalNode___closed__2;
x_4 = lean_array_push(x_3, x_2);
x_5 = l_Lean_Meta_mkDecideProof___rarg___closed__2;
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1), 7, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Lean_Meta_mkDecideProof___rarg___closed__3;
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkDecideProof(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkDecideProof___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLess");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLt___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Less");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLt___rarg___closed__2;
x_2 = l_Lean_Meta_mkLt___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_mkAppStx___closed__9;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_array_push(x_5, x_3);
x_7 = l_Lean_Meta_mkLt___rarg___closed__4;
x_8 = l_Lean_Meta_mkAppM___rarg(x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLt___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLessEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLe___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LessEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLe___rarg___closed__2;
x_2 = l_Lean_Meta_mkLe___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkLe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_mkAppStx___closed__9;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_array_push(x_5, x_3);
x_7 = l_Lean_Meta_mkLe___rarg___closed__4;
x_8 = l_Lean_Meta_mkAppM___rarg(x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkLe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkLe___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Structure(lean_object*);
lean_object* initialize_Lean_Util_Recognizers(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_AppBuilder(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1);
l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2);
l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__1);
l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2);
l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__1);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__2);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__3);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__5);
l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6 = _init_l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6);
l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__1);
l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2);
l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3);
l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4);
l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5);
l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1);
l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2);
l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__1);
l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__2);
l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__3);
l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4);
l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__1);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__3);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__4);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__6);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7);
l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8 = _init_l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8);
l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__1);
l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__2);
l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__3);
l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__4);
l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_15__mkCongrArgImp___closed__5);
l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__1);
l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2);
l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__3);
l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__4);
l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__5);
l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__1);
l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_17__mkCongrImp___closed__2);
l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1 = _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__1);
l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2 = _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__2);
l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3 = _init_l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__1);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__3);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__4);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__6);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7);
l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8 = _init_l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8);
l_Lean_Meta_mkAppM___rarg___closed__1 = _init_l_Lean_Meta_mkAppM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__1);
l_Lean_Meta_mkAppM___rarg___closed__2 = _init_l_Lean_Meta_mkAppM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__2);
l_Lean_Meta_mkAppM___rarg___closed__3 = _init_l_Lean_Meta_mkAppM___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__3);
l_Lean_Meta_mkAppM___rarg___closed__4 = _init_l_Lean_Meta_mkAppM___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1 = _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1);
l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2 = _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2);
l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3 = _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__3);
l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4 = _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__4);
l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5 = _init_l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5);
l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6 = _init_l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6);
l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1);
l_Lean_Meta_mkEqMP___rarg___closed__1 = _init_l_Lean_Meta_mkEqMP___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMP___rarg___closed__1);
l_Lean_Meta_mkEqMP___rarg___closed__2 = _init_l_Lean_Meta_mkEqMP___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMP___rarg___closed__2);
l_Lean_Meta_mkEqMPR___rarg___closed__1 = _init_l_Lean_Meta_mkEqMPR___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___rarg___closed__1);
l_Lean_Meta_mkEqMPR___rarg___closed__2 = _init_l_Lean_Meta_mkEqMPR___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___rarg___closed__2);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__3);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__7);
l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8 = _init_l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8);
l_Lean_Meta_mkPure___rarg___closed__1 = _init_l_Lean_Meta_mkPure___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__1);
l_Lean_Meta_mkPure___rarg___closed__2 = _init_l_Lean_Meta_mkPure___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__2);
l_Lean_Meta_mkPure___rarg___closed__3 = _init_l_Lean_Meta_mkPure___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__3);
l_Lean_Meta_mkPure___rarg___closed__4 = _init_l_Lean_Meta_mkPure___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__1);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__2);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__3);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__4);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__5);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__6);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__8);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__9);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11);
l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12 = _init_l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__12);
l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1);
l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2);
l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3);
l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4 = _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4);
l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1);
l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2);
l_Lean_Meta_mkDecideProof___rarg___closed__1 = _init_l_Lean_Meta_mkDecideProof___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___rarg___closed__1);
l_Lean_Meta_mkDecideProof___rarg___closed__2 = _init_l_Lean_Meta_mkDecideProof___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___rarg___closed__2);
l_Lean_Meta_mkDecideProof___rarg___closed__3 = _init_l_Lean_Meta_mkDecideProof___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___rarg___closed__3);
l_Lean_Meta_mkLt___rarg___closed__1 = _init_l_Lean_Meta_mkLt___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLt___rarg___closed__1);
l_Lean_Meta_mkLt___rarg___closed__2 = _init_l_Lean_Meta_mkLt___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLt___rarg___closed__2);
l_Lean_Meta_mkLt___rarg___closed__3 = _init_l_Lean_Meta_mkLt___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLt___rarg___closed__3);
l_Lean_Meta_mkLt___rarg___closed__4 = _init_l_Lean_Meta_mkLt___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLt___rarg___closed__4);
l_Lean_Meta_mkLe___rarg___closed__1 = _init_l_Lean_Meta_mkLe___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLe___rarg___closed__1);
l_Lean_Meta_mkLe___rarg___closed__2 = _init_l_Lean_Meta_mkLe___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLe___rarg___closed__2);
l_Lean_Meta_mkLe___rarg___closed__3 = _init_l_Lean_Meta_mkLe___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLe___rarg___closed__3);
l_Lean_Meta_mkLe___rarg___closed__4 = _init_l_Lean_Meta_mkLe___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLe___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
