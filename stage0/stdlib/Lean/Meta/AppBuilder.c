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
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Meta_mkSorry___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__7;
lean_object* l_Lean_Meta_mkProjection___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__7;
lean_object* l_Lean_Meta_mkEqRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_7__infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__11;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__4;
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__3;
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_listToExpr___rarg___closed__4;
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
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__1;
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_5__inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__4;
lean_object* l_Lean_Meta_mkAppM___rarg___closed__1;
lean_object* l_Lean_Meta_mkArrayLit(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkDecIsTrue___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkHEqTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__4;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5;
lean_object* l_Lean_Meta_mkId___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
lean_object* l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__3;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__1;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure(lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_26__mkListLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException(lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_20__mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
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
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
lean_object* l_Lean_Meta_mkListLit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__1;
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
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
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_16__mkCongrFunImp___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_11__mkEqTransImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5;
extern lean_object* l_Lean_listToExpr___rarg___closed__6;
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
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
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
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_indentExpr(x_3);
x_5 = l_Lean_MessageData_ofList___closed__3;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_KernelException_toMessageData___closed__12;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_indentExpr(x_9);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg___closed__6;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(9, 2, 0);
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
x_17 = lean_alloc_ctor(9, 2, 0);
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
x_57 = lean_alloc_ctor(9, 2, 0);
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
x_22 = lean_alloc_ctor(9, 2, 0);
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
x_17 = lean_alloc_ctor(9, 2, 0);
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
x_61 = lean_alloc_ctor(9, 2, 0);
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
x_23 = lean_alloc_ctor(9, 2, 0);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_indentExpr(x_13);
x_15 = l___private_Lean_Meta_AppBuilder_12__mkHEqSymmImp___closed__4;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_AppBuilder_13__mkHEqTransImp___closed__1;
x_18 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_17, x_16, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = l_Lean_Expr_appFn_x21(x_8);
x_20 = l_Lean_Expr_appFn_x21(x_19);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_24 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_25 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
lean_inc(x_22);
x_26 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_22, x_24, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_1);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_31 = l_Lean_indentExpr(x_30);
x_32 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__5;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_MessageData_ofList___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__8;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_24);
x_39 = l_Lean_indentExpr(x_38);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_42 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_41, x_40, x_2, x_3, x_4, x_5, x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_dec(x_26);
lean_inc(x_22);
x_48 = l___private_Lean_Meta_InferType_4__getLevelImp(x_22, x_2, x_3, x_4, x_5, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_54 = l_Lean_mkConst(x_53, x_52);
x_55 = l_Lean_mkApp4(x_54, x_22, x_23, x_25, x_1);
lean_ctor_set(x_48, 0, x_55);
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp___closed__2;
x_61 = l_Lean_mkConst(x_60, x_59);
x_62 = l_Lean_mkApp4(x_61, x_22, x_23, x_25, x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_48);
if (x_64 == 0)
{
return x_48;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_48, 0);
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_48);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
return x_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_26, 0);
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_26);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_7);
if (x_72 == 0)
{
return x_7;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_7, 0);
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_7);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
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
x_18 = lean_alloc_ctor(9, 2, 0);
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
x_60 = lean_alloc_ctor(9, 2, 0);
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
x_69 = lean_alloc_ctor(9, 2, 0);
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
x_16 = lean_alloc_ctor(9, 2, 0);
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
lean_dec(x_34);
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
x_30 = lean_alloc_ctor(9, 2, 0);
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
x_83 = lean_alloc_ctor(9, 2, 0);
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
x_19 = lean_alloc_ctor(9, 2, 0);
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
x_36 = lean_alloc_ctor(9, 2, 0);
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
x_17 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f___spec__9(x_15, x_5, x_6, x_7, x_8, x_16);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_15);
x_26 = l_Lean_indentExpr(x_25);
x_27 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_1, x_28, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_81; lean_object* x_82; 
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_48 = lean_array_get_size(x_4);
x_49 = lean_expr_instantiate_rev_range(x_45, x_5, x_48, x_4);
lean_dec(x_48);
lean_dec(x_45);
x_81 = (uint8_t)((x_47 << 24) >> 61);
x_82 = lean_box(x_81);
switch (lean_obj_tag(x_82)) {
case 1:
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_49);
x_84 = 0;
lean_inc(x_8);
x_85 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_83, x_84, x_44, x_8, x_9, x_10, x_11, x_12);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_array_push(x_4, x_86);
x_4 = x_88;
x_7 = x_46;
x_12 = x_87;
goto _start;
}
case 3:
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_49);
x_91 = 1;
lean_inc(x_8);
x_92 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_90, x_91, x_44, x_8, x_9, x_10, x_11, x_12);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_93);
x_95 = lean_array_push(x_4, x_93);
x_96 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
x_97 = lean_array_push(x_6, x_96);
x_4 = x_95;
x_6 = x_97;
x_7 = x_46;
x_12 = x_94;
goto _start;
}
default: 
{
lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_44);
x_99 = lean_box(0);
x_50 = x_99;
goto block_80;
}
}
block_80:
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_50);
x_51 = lean_array_get_size(x_2);
x_52 = lean_nat_dec_lt(x_3, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_3);
x_53 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_54 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_53, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_55);
x_56 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_55, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_59 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_49, x_57, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_63, x_1);
lean_dec(x_4);
x_65 = l_Lean_MessageData_Inhabited___closed__1;
x_66 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_64, x_55, x_65, x_8, x_9, x_10, x_11, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_3, x_68);
lean_dec(x_3);
x_70 = lean_array_push(x_4, x_55);
x_3 = x_69;
x_4 = x_70;
x_7 = x_46;
x_12 = x_67;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
return x_59;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_59, 0);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_59);
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
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_56);
if (x_76 == 0)
{
return x_56;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_56, 0);
x_78 = lean_ctor_get(x_56, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_56);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
x_13 = x_100;
goto block_43;
}
block_43:
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = l_Lean_indentExpr(x_22);
x_24 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__5;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_MessageData_ofList___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_32 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_30, x_31);
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_35 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_34, x_33, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__2;
x_37 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_36, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_6);
lean_dec(x_4);
return x_37;
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
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImpl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (x_4 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_3);
x_23 = lean_st_ref_get(x_8, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_8, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 2);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_35 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_35);
x_36 = lean_st_ref_set(x_8, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_71 = lean_st_ref_get(x_6, x_37);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_take(x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = l_Lean_MetavarContext_incDepth(x_79);
lean_ctor_set(x_76, 0, x_80);
x_81 = lean_st_ref_set(x_6, x_76, x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_87, x_2, x_89, x_90, x_89, x_90, x_88, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_8, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 2);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get_uint8(x_99, sizeof(void*)*1);
lean_dec(x_99);
x_101 = lean_st_ref_take(x_8, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_102, 2);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_27);
x_108 = lean_st_ref_set(x_8, x_102, x_104);
lean_dec(x_8);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
x_111 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_111);
lean_ctor_set(x_84, 0, x_92);
lean_ctor_set(x_108, 0, x_84);
x_10 = x_108;
goto block_22;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_113);
lean_ctor_set(x_84, 0, x_92);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_84);
lean_ctor_set(x_114, 1, x_112);
x_10 = x_114;
goto block_22;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_103, 0);
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_27);
lean_ctor_set(x_102, 2, x_116);
x_117 = lean_st_ref_set(x_8, x_102, x_104);
lean_dec(x_8);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_120);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_84);
lean_ctor_set(x_121, 1, x_118);
x_10 = x_121;
goto block_22;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_102, 0);
x_123 = lean_ctor_get(x_102, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_102);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_125 = x_103;
} else {
 lean_dec_ref(x_103);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 1, 1);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_27);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_126);
x_128 = lean_st_ref_set(x_8, x_127, x_104);
lean_dec(x_8);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_131);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_84);
lean_ctor_set(x_132, 1, x_129);
x_10 = x_132;
goto block_22;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_84);
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_91, 1);
lean_inc(x_134);
lean_dec(x_91);
x_135 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_38 = x_133;
x_39 = x_136;
goto block_70;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_84, 0);
x_138 = lean_ctor_get(x_84, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_84);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_141 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_137, x_2, x_139, x_140, x_139, x_140, x_138, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_143);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_get(x_8, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 2);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get_uint8(x_149, sizeof(void*)*1);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_8, x_148);
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
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_st_ref_set(x_8, x_161, x_154);
lean_dec(x_8);
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
x_165 = lean_box(x_150);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
x_10 = x_167;
goto block_22;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_141, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_141, 1);
lean_inc(x_169);
lean_dec(x_141);
x_170 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_38 = x_168;
x_39 = x_171;
goto block_70;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_83, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_83, 1);
lean_inc(x_173);
lean_dec(x_83);
x_174 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_173);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_38 = x_172;
x_39 = x_175;
goto block_70;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_76, 0);
x_177 = lean_ctor_get(x_76, 1);
x_178 = lean_ctor_get(x_76, 2);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_76);
x_179 = l_Lean_MetavarContext_incDepth(x_176);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
x_181 = lean_st_ref_set(x_6, x_180, x_77);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_191 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_186, x_2, x_189, x_190, x_189, x_190, x_187, x_5, x_6, x_7, x_8, x_185);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_193);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_st_ref_get(x_8, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 2);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get_uint8(x_199, sizeof(void*)*1);
lean_dec(x_199);
x_201 = lean_st_ref_take(x_8, x_198);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 1, 1);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_207)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_207;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_206);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_st_ref_set(x_8, x_211, x_204);
lean_dec(x_8);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = lean_box(x_200);
if (lean_is_scalar(x_188)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_188;
}
lean_ctor_set(x_216, 0, x_192);
lean_ctor_set(x_216, 1, x_215);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
x_10 = x_217;
goto block_22;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_188);
x_218 = lean_ctor_get(x_191, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_191, 1);
lean_inc(x_219);
lean_dec(x_191);
x_220 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_219);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_38 = x_218;
x_39 = x_221;
goto block_70;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_183, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 1);
lean_inc(x_223);
lean_dec(x_183);
x_224 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_223);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_38 = x_222;
x_39 = x_225;
goto block_70;
}
}
block_70:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_st_ref_get(x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 2);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_27);
x_49 = lean_st_ref_set(x_8, x_43, x_45);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_38);
x_10 = x_49;
goto block_22;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
x_10 = x_53;
goto block_22;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_27);
lean_ctor_set(x_43, 2, x_55);
x_56 = lean_st_ref_set(x_8, x_43, x_45);
lean_dec(x_8);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_57);
x_10 = x_59;
goto block_22;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_63 = x_44;
} else {
 lean_dec_ref(x_44);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_27);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_st_ref_set(x_8, x_65, x_45);
lean_dec(x_8);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_67);
x_10 = x_69;
goto block_22;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_226 = lean_ctor_get(x_30, 0);
lean_inc(x_226);
lean_dec(x_30);
x_227 = 0;
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_227);
lean_ctor_set(x_29, 2, x_228);
x_229 = lean_st_ref_set(x_8, x_29, x_31);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_251 = lean_st_ref_get(x_6, x_230);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_st_ref_take(x_6, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 2);
lean_inc(x_260);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_261 = x_256;
} else {
 lean_dec_ref(x_256);
 x_261 = lean_box(0);
}
x_262 = l_Lean_MetavarContext_incDepth(x_258);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 3, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
lean_ctor_set(x_263, 2, x_260);
x_264 = lean_st_ref_set(x_6, x_263, x_257);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_274 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_269, x_2, x_272, x_273, x_272, x_273, x_270, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_276);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_st_ref_get(x_8, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 2);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get_uint8(x_282, sizeof(void*)*1);
lean_dec(x_282);
x_284 = lean_st_ref_take(x_8, x_281);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_285, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 x_290 = x_285;
} else {
 lean_dec_ref(x_285);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_286, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_292 = x_286;
} else {
 lean_dec_ref(x_286);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 1, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 3, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_289);
lean_ctor_set(x_294, 2, x_293);
x_295 = lean_st_ref_set(x_8, x_294, x_287);
lean_dec(x_8);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = lean_box(x_283);
if (lean_is_scalar(x_271)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_271;
}
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_296);
x_10 = x_300;
goto block_22;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_271);
x_301 = lean_ctor_get(x_274, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_274, 1);
lean_inc(x_302);
lean_dec(x_274);
x_303 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_231 = x_301;
x_232 = x_304;
goto block_250;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_266, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_266, 1);
lean_inc(x_306);
lean_dec(x_266);
x_307 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_306);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec(x_307);
x_231 = x_305;
x_232 = x_308;
goto block_250;
}
block_250:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_233 = lean_st_ref_get(x_8, x_232);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_st_ref_take(x_8, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_237, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 1, 1);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_241)) {
 x_245 = lean_alloc_ctor(0, 3, 0);
} else {
 x_245 = x_241;
}
lean_ctor_set(x_245, 0, x_239);
lean_ctor_set(x_245, 1, x_240);
lean_ctor_set(x_245, 2, x_244);
x_246 = lean_st_ref_set(x_8, x_245, x_238);
lean_dec(x_8);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_231);
lean_ctor_set(x_249, 1, x_247);
x_10 = x_249;
goto block_22;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_309 = lean_ctor_get(x_29, 0);
x_310 = lean_ctor_get(x_29, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_29);
x_311 = lean_ctor_get(x_30, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_312 = x_30;
} else {
 lean_dec_ref(x_30);
 x_312 = lean_box(0);
}
x_313 = 0;
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 1, 1);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_315, 0, x_309);
lean_ctor_set(x_315, 1, x_310);
lean_ctor_set(x_315, 2, x_314);
x_316 = lean_st_ref_set(x_8, x_315, x_31);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_338 = lean_st_ref_get(x_6, x_317);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_st_ref_take(x_6, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 2);
lean_inc(x_347);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 x_348 = x_343;
} else {
 lean_dec_ref(x_343);
 x_348 = lean_box(0);
}
x_349 = l_Lean_MetavarContext_incDepth(x_345);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 3, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_346);
lean_ctor_set(x_350, 2, x_347);
x_351 = lean_st_ref_set(x_6, x_350, x_344);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_358 = x_354;
} else {
 lean_dec_ref(x_354);
 x_358 = lean_box(0);
}
x_359 = lean_unsigned_to_nat(0u);
x_360 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_361 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_356, x_2, x_359, x_360, x_359, x_360, x_357, x_5, x_6, x_7, x_8, x_355);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_st_ref_get(x_8, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 2);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get_uint8(x_369, sizeof(void*)*1);
lean_dec(x_369);
x_371 = lean_st_ref_take(x_8, x_368);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_372, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 x_377 = x_372;
} else {
 lean_dec_ref(x_372);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_373, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_379 = x_373;
} else {
 lean_dec_ref(x_373);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 1, 1);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_377)) {
 x_381 = lean_alloc_ctor(0, 3, 0);
} else {
 x_381 = x_377;
}
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_381, 1, x_376);
lean_ctor_set(x_381, 2, x_380);
x_382 = lean_st_ref_set(x_8, x_381, x_374);
lean_dec(x_8);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = lean_box(x_370);
if (lean_is_scalar(x_358)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_358;
}
lean_ctor_set(x_386, 0, x_362);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_384;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_383);
x_10 = x_387;
goto block_22;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_358);
x_388 = lean_ctor_get(x_361, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_361, 1);
lean_inc(x_389);
lean_dec(x_361);
x_390 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_389);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_318 = x_388;
x_319 = x_391;
goto block_337;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_353, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_353, 1);
lean_inc(x_393);
lean_dec(x_353);
x_394 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_393);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_318 = x_392;
x_319 = x_395;
goto block_337;
}
block_337:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_320 = lean_st_ref_get(x_8, x_319);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_st_ref_take(x_8, x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_323, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 lean_ctor_release(x_323, 2);
 x_328 = x_323;
} else {
 lean_dec_ref(x_323);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_324, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_330 = x_324;
} else {
 lean_dec_ref(x_324);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 1);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_328)) {
 x_332 = lean_alloc_ctor(0, 3, 0);
} else {
 x_332 = x_328;
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_327);
lean_ctor_set(x_332, 2, x_331);
x_333 = lean_st_ref_set(x_8, x_332, x_325);
lean_dec(x_8);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
 lean_ctor_set_tag(x_336, 1);
}
lean_ctor_set(x_336, 0, x_318);
lean_ctor_set(x_336, 1, x_334);
x_10 = x_336;
goto block_22;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_396 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_8, x_9);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_407 = lean_st_ref_get(x_6, x_398);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_st_ref_take(x_6, x_409);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = !lean_is_exclusive(x_412);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_412, 0);
x_416 = l_Lean_MetavarContext_incDepth(x_415);
lean_ctor_set(x_412, 0, x_416);
x_417 = lean_st_ref_set(x_6, x_412, x_413);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_unsigned_to_nat(0u);
x_425 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_426 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_422, x_2, x_424, x_425, x_424, x_425, x_423, x_5, x_6, x_7, x_8, x_421);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_428);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec(x_429);
x_431 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_430);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_432 = !lean_is_exclusive(x_431);
if (x_432 == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_431, 0);
lean_dec(x_433);
lean_ctor_set(x_431, 0, x_427);
return x_431;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_427);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_436 = lean_ctor_get(x_426, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_426, 1);
lean_inc(x_437);
lean_dec(x_426);
x_438 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_437);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
lean_dec(x_438);
x_399 = x_436;
x_400 = x_439;
goto block_406;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_419, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_419, 1);
lean_inc(x_441);
lean_dec(x_419);
x_442 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_441);
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_399 = x_440;
x_400 = x_443;
goto block_406;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_444 = lean_ctor_get(x_412, 0);
x_445 = lean_ctor_get(x_412, 1);
x_446 = lean_ctor_get(x_412, 2);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_412);
x_447 = l_Lean_MetavarContext_incDepth(x_444);
x_448 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
lean_ctor_set(x_448, 2, x_446);
x_449 = lean_st_ref_set(x_6, x_448, x_413);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
x_456 = lean_unsigned_to_nat(0u);
x_457 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_458 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_454, x_2, x_456, x_457, x_456, x_457, x_455, x_5, x_6, x_7, x_8, x_453);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_460);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
lean_dec(x_461);
x_463 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_462);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_459);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_458, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_458, 1);
lean_inc(x_468);
lean_dec(x_458);
x_469 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_468);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_399 = x_467;
x_400 = x_470;
goto block_406;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_451, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_451, 1);
lean_inc(x_472);
lean_dec(x_451);
x_473 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_472);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_399 = x_471;
x_400 = x_474;
goto block_406;
}
}
block_406:
{
lean_object* x_401; uint8_t x_402; 
x_401 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_400);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_401, 0);
lean_dec(x_403);
lean_ctor_set_tag(x_401, 1);
lean_ctor_set(x_401, 0, x_399);
return x_401;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_399);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
block_22:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
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
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__2___boxed), 9, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkAppM___rarg___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_50 = lean_array_get_size(x_4);
x_51 = lean_expr_instantiate_rev_range(x_47, x_5, x_50, x_4);
lean_dec(x_50);
lean_dec(x_47);
x_52 = lean_array_get_size(x_2);
x_53 = lean_nat_dec_lt(x_3, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_3);
x_54 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_55 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_54, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; lean_object* x_58; 
x_57 = (uint8_t)((x_49 << 24) >> 61);
x_58 = lean_box(x_57);
if (lean_obj_tag(x_58) == 3)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_51);
x_60 = 1;
lean_inc(x_8);
x_61 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_59, x_60, x_46, x_8, x_9, x_10, x_11, x_12);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_3, x_64);
lean_dec(x_3);
lean_inc(x_62);
x_66 = lean_array_push(x_4, x_62);
x_67 = l_Lean_Expr_mvarId_x21(x_62);
lean_dec(x_62);
x_68 = lean_array_push(x_6, x_67);
x_3 = x_65;
x_4 = x_66;
x_6 = x_68;
x_7 = x_48;
x_12 = x_63;
goto _start;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_58);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_51);
x_71 = 0;
lean_inc(x_8);
x_72 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_70, x_71, x_46, x_8, x_9, x_10, x_11, x_12);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_3, x_75);
lean_dec(x_3);
x_77 = lean_array_push(x_4, x_73);
x_3 = x_76;
x_4 = x_77;
x_7 = x_48;
x_12 = x_74;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_46);
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
lean_dec(x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_79);
x_80 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_79, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_83 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_51, x_81, x_8, x_9, x_10, x_11, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_87, x_1);
lean_dec(x_4);
x_89 = l_Lean_MessageData_Inhabited___closed__1;
x_90 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_88, x_79, x_89, x_8, x_9, x_10, x_11, x_86);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_3, x_92);
lean_dec(x_3);
x_94 = lean_array_push(x_4, x_79);
x_3 = x_93;
x_4 = x_94;
x_7 = x_48;
x_12 = x_91;
goto _start;
}
}
else
{
uint8_t x_96; 
lean_dec(x_79);
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_83);
if (x_96 == 0)
{
return x_83;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_83, 0);
x_98 = lean_ctor_get(x_83, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_83);
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
lean_dec(x_79);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_80);
if (x_100 == 0)
{
return x_80;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_80, 0);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_80);
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
lean_object* x_104; 
x_104 = lean_box(0);
x_13 = x_104;
goto block_45;
}
block_45:
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_empty___closed__1;
x_24 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___spec__1(x_2, x_2, x_22, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = l_Lean_indentExpr(x_25);
x_27 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_MessageData_ofList___closed__3;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main___closed__8;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_34 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_24, x_22, x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_37 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_36, x_35, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main___closed__2;
x_39 = l___private_Lean_Meta_AppBuilder_18__mkAppMFinal(x_38, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_6);
lean_dec(x_4);
return x_39;
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
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (x_4 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_3);
x_23 = lean_st_ref_get(x_8, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_8, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 2);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_35 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_35);
x_36 = lean_st_ref_set(x_8, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_71 = lean_st_ref_get(x_6, x_37);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_take(x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = l_Lean_MetavarContext_incDepth(x_79);
lean_ctor_set(x_76, 0, x_80);
x_81 = lean_st_ref_set(x_6, x_76, x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_87, x_2, x_89, x_90, x_89, x_90, x_88, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_8, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 2);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get_uint8(x_99, sizeof(void*)*1);
lean_dec(x_99);
x_101 = lean_st_ref_take(x_8, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_102, 2);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_27);
x_108 = lean_st_ref_set(x_8, x_102, x_104);
lean_dec(x_8);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
x_111 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_111);
lean_ctor_set(x_84, 0, x_92);
lean_ctor_set(x_108, 0, x_84);
x_10 = x_108;
goto block_22;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_113);
lean_ctor_set(x_84, 0, x_92);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_84);
lean_ctor_set(x_114, 1, x_112);
x_10 = x_114;
goto block_22;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_103, 0);
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_27);
lean_ctor_set(x_102, 2, x_116);
x_117 = lean_st_ref_set(x_8, x_102, x_104);
lean_dec(x_8);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_120);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_84);
lean_ctor_set(x_121, 1, x_118);
x_10 = x_121;
goto block_22;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_102, 0);
x_123 = lean_ctor_get(x_102, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_102);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_125 = x_103;
} else {
 lean_dec_ref(x_103);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 1, 1);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_27);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_126);
x_128 = lean_st_ref_set(x_8, x_127, x_104);
lean_dec(x_8);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_131);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_84);
lean_ctor_set(x_132, 1, x_129);
x_10 = x_132;
goto block_22;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_84);
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_91, 1);
lean_inc(x_134);
lean_dec(x_91);
x_135 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_38 = x_133;
x_39 = x_136;
goto block_70;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_84, 0);
x_138 = lean_ctor_get(x_84, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_84);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_141 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_137, x_2, x_139, x_140, x_139, x_140, x_138, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_143);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_get(x_8, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 2);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get_uint8(x_149, sizeof(void*)*1);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_8, x_148);
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
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_st_ref_set(x_8, x_161, x_154);
lean_dec(x_8);
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
x_165 = lean_box(x_150);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
x_10 = x_167;
goto block_22;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_141, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_141, 1);
lean_inc(x_169);
lean_dec(x_141);
x_170 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_38 = x_168;
x_39 = x_171;
goto block_70;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_83, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_83, 1);
lean_inc(x_173);
lean_dec(x_83);
x_174 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_173);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_38 = x_172;
x_39 = x_175;
goto block_70;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_76, 0);
x_177 = lean_ctor_get(x_76, 1);
x_178 = lean_ctor_get(x_76, 2);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_76);
x_179 = l_Lean_MetavarContext_incDepth(x_176);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
x_181 = lean_st_ref_set(x_6, x_180, x_77);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_191 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_186, x_2, x_189, x_190, x_189, x_190, x_187, x_5, x_6, x_7, x_8, x_185);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_193);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_st_ref_get(x_8, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 2);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get_uint8(x_199, sizeof(void*)*1);
lean_dec(x_199);
x_201 = lean_st_ref_take(x_8, x_198);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 1, 1);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_207)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_207;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_206);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_st_ref_set(x_8, x_211, x_204);
lean_dec(x_8);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = lean_box(x_200);
if (lean_is_scalar(x_188)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_188;
}
lean_ctor_set(x_216, 0, x_192);
lean_ctor_set(x_216, 1, x_215);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
x_10 = x_217;
goto block_22;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_188);
x_218 = lean_ctor_get(x_191, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_191, 1);
lean_inc(x_219);
lean_dec(x_191);
x_220 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_219);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_38 = x_218;
x_39 = x_221;
goto block_70;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_183, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 1);
lean_inc(x_223);
lean_dec(x_183);
x_224 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_5, x_6, x_7, x_8, x_223);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_38 = x_222;
x_39 = x_225;
goto block_70;
}
}
block_70:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_st_ref_get(x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 2);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_27);
x_49 = lean_st_ref_set(x_8, x_43, x_45);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_38);
x_10 = x_49;
goto block_22;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
x_10 = x_53;
goto block_22;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_27);
lean_ctor_set(x_43, 2, x_55);
x_56 = lean_st_ref_set(x_8, x_43, x_45);
lean_dec(x_8);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_57);
x_10 = x_59;
goto block_22;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_63 = x_44;
} else {
 lean_dec_ref(x_44);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_27);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_st_ref_set(x_8, x_65, x_45);
lean_dec(x_8);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_67);
x_10 = x_69;
goto block_22;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_226 = lean_ctor_get(x_30, 0);
lean_inc(x_226);
lean_dec(x_30);
x_227 = 0;
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_227);
lean_ctor_set(x_29, 2, x_228);
x_229 = lean_st_ref_set(x_8, x_29, x_31);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_251 = lean_st_ref_get(x_6, x_230);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_st_ref_take(x_6, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 2);
lean_inc(x_260);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_261 = x_256;
} else {
 lean_dec_ref(x_256);
 x_261 = lean_box(0);
}
x_262 = l_Lean_MetavarContext_incDepth(x_258);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 3, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
lean_ctor_set(x_263, 2, x_260);
x_264 = lean_st_ref_set(x_6, x_263, x_257);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_274 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_269, x_2, x_272, x_273, x_272, x_273, x_270, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_276);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_st_ref_get(x_8, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 2);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get_uint8(x_282, sizeof(void*)*1);
lean_dec(x_282);
x_284 = lean_st_ref_take(x_8, x_281);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_285, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 x_290 = x_285;
} else {
 lean_dec_ref(x_285);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_286, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_292 = x_286;
} else {
 lean_dec_ref(x_286);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 1, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 3, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_289);
lean_ctor_set(x_294, 2, x_293);
x_295 = lean_st_ref_set(x_8, x_294, x_287);
lean_dec(x_8);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = lean_box(x_283);
if (lean_is_scalar(x_271)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_271;
}
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_296);
x_10 = x_300;
goto block_22;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_271);
x_301 = lean_ctor_get(x_274, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_274, 1);
lean_inc(x_302);
lean_dec(x_274);
x_303 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_231 = x_301;
x_232 = x_304;
goto block_250;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_266, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_266, 1);
lean_inc(x_306);
lean_dec(x_266);
x_307 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_5, x_6, x_7, x_8, x_306);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec(x_307);
x_231 = x_305;
x_232 = x_308;
goto block_250;
}
block_250:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_233 = lean_st_ref_get(x_8, x_232);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_st_ref_take(x_8, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_237, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 1, 1);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_241)) {
 x_245 = lean_alloc_ctor(0, 3, 0);
} else {
 x_245 = x_241;
}
lean_ctor_set(x_245, 0, x_239);
lean_ctor_set(x_245, 1, x_240);
lean_ctor_set(x_245, 2, x_244);
x_246 = lean_st_ref_set(x_8, x_245, x_238);
lean_dec(x_8);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_231);
lean_ctor_set(x_249, 1, x_247);
x_10 = x_249;
goto block_22;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_309 = lean_ctor_get(x_29, 0);
x_310 = lean_ctor_get(x_29, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_29);
x_311 = lean_ctor_get(x_30, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_312 = x_30;
} else {
 lean_dec_ref(x_30);
 x_312 = lean_box(0);
}
x_313 = 0;
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 1, 1);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_315, 0, x_309);
lean_ctor_set(x_315, 1, x_310);
lean_ctor_set(x_315, 2, x_314);
x_316 = lean_st_ref_set(x_8, x_315, x_31);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_338 = lean_st_ref_get(x_6, x_317);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_st_ref_take(x_6, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 2);
lean_inc(x_347);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 x_348 = x_343;
} else {
 lean_dec_ref(x_343);
 x_348 = lean_box(0);
}
x_349 = l_Lean_MetavarContext_incDepth(x_345);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 3, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_346);
lean_ctor_set(x_350, 2, x_347);
x_351 = lean_st_ref_set(x_6, x_350, x_344);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_358 = x_354;
} else {
 lean_dec_ref(x_354);
 x_358 = lean_box(0);
}
x_359 = lean_unsigned_to_nat(0u);
x_360 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_361 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_356, x_2, x_359, x_360, x_359, x_360, x_357, x_5, x_6, x_7, x_8, x_355);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_st_ref_get(x_8, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 2);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get_uint8(x_369, sizeof(void*)*1);
lean_dec(x_369);
x_371 = lean_st_ref_take(x_8, x_368);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_372, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 x_377 = x_372;
} else {
 lean_dec_ref(x_372);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_373, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_379 = x_373;
} else {
 lean_dec_ref(x_373);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 1, 1);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_377)) {
 x_381 = lean_alloc_ctor(0, 3, 0);
} else {
 x_381 = x_377;
}
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_381, 1, x_376);
lean_ctor_set(x_381, 2, x_380);
x_382 = lean_st_ref_set(x_8, x_381, x_374);
lean_dec(x_8);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = lean_box(x_370);
if (lean_is_scalar(x_358)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_358;
}
lean_ctor_set(x_386, 0, x_362);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_384;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_383);
x_10 = x_387;
goto block_22;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_358);
x_388 = lean_ctor_get(x_361, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_361, 1);
lean_inc(x_389);
lean_dec(x_361);
x_390 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_389);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_318 = x_388;
x_319 = x_391;
goto block_337;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_353, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_353, 1);
lean_inc(x_393);
lean_dec(x_353);
x_394 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_5, x_6, x_7, x_8, x_393);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_318 = x_392;
x_319 = x_395;
goto block_337;
}
block_337:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_320 = lean_st_ref_get(x_8, x_319);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_st_ref_take(x_8, x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_323, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 lean_ctor_release(x_323, 2);
 x_328 = x_323;
} else {
 lean_dec_ref(x_323);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_324, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_330 = x_324;
} else {
 lean_dec_ref(x_324);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 1);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_328)) {
 x_332 = lean_alloc_ctor(0, 3, 0);
} else {
 x_332 = x_328;
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_327);
lean_ctor_set(x_332, 2, x_331);
x_333 = lean_st_ref_set(x_8, x_332, x_325);
lean_dec(x_8);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
 lean_ctor_set_tag(x_336, 1);
}
lean_ctor_set(x_336, 0, x_318);
lean_ctor_set(x_336, 1, x_334);
x_10 = x_336;
goto block_22;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_396 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_8, x_9);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_407 = lean_st_ref_get(x_6, x_398);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_st_ref_take(x_6, x_409);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = !lean_is_exclusive(x_412);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_412, 0);
x_416 = l_Lean_MetavarContext_incDepth(x_415);
lean_ctor_set(x_412, 0, x_416);
x_417 = lean_st_ref_set(x_6, x_412, x_413);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_unsigned_to_nat(0u);
x_425 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_426 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_422, x_2, x_424, x_425, x_424, x_425, x_423, x_5, x_6, x_7, x_8, x_421);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_428);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec(x_429);
x_431 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_430);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_432 = !lean_is_exclusive(x_431);
if (x_432 == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_431, 0);
lean_dec(x_433);
lean_ctor_set(x_431, 0, x_427);
return x_431;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_427);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_436 = lean_ctor_get(x_426, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_426, 1);
lean_inc(x_437);
lean_dec(x_426);
x_438 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_437);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
lean_dec(x_438);
x_399 = x_436;
x_400 = x_439;
goto block_406;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_419, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_419, 1);
lean_inc(x_441);
lean_dec(x_419);
x_442 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_441);
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_399 = x_440;
x_400 = x_443;
goto block_406;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_444 = lean_ctor_get(x_412, 0);
x_445 = lean_ctor_get(x_412, 1);
x_446 = lean_ctor_get(x_412, 2);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_412);
x_447 = l_Lean_MetavarContext_incDepth(x_444);
x_448 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
lean_ctor_set(x_448, 2, x_446);
x_449 = lean_st_ref_set(x_6, x_448, x_413);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_5, x_6, x_7, x_8, x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
x_456 = lean_unsigned_to_nat(0u);
x_457 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_458 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_454, x_2, x_456, x_457, x_456, x_457, x_455, x_5, x_6, x_7, x_8, x_453);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_460);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
lean_dec(x_461);
x_463 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_462);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_459);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_458, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_458, 1);
lean_inc(x_468);
lean_dec(x_458);
x_469 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_468);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_399 = x_467;
x_400 = x_470;
goto block_406;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_451, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_451, 1);
lean_inc(x_472);
lean_dec(x_451);
x_473 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_410, x_5, x_6, x_7, x_8, x_472);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_399 = x_471;
x_400 = x_474;
goto block_406;
}
}
block_406:
{
lean_object* x_401; uint8_t x_402; 
x_401 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_3, x_5, x_6, x_7, x_8, x_400);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_401, 0);
lean_dec(x_403);
lean_ctor_set_tag(x_401, 1);
lean_ctor_set(x_401, 0, x_399);
return x_401;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_399);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
block_22:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
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
}
}
lean_object* l_Lean_Meta_mkAppOptM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed), 9, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
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
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkAppOptM___rarg___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
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
x_19 = lean_alloc_ctor(9, 2, 0);
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
lean_object* x_42; 
x_42 = lean_ctor_get(x_32, 2);
lean_inc(x_42);
lean_dec(x_32);
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
x_47 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
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
goto block_41;
}
}
else
{
lean_object* x_59; 
lean_free_object(x_30);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_34 = x_59;
goto block_41;
}
block_41:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_indentExpr(x_35);
x_37 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_40 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_39, x_38, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_30, 0);
x_61 = lean_ctor_get(x_30, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_30);
if (lean_obj_tag(x_60) == 7)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_60, 2);
lean_inc(x_70);
lean_dec(x_60);
if (lean_obj_tag(x_70) == 3)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_28);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_76 = l_Lean_mkConst(x_75, x_74);
x_77 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_78 = lean_array_push(x_77, x_24);
x_79 = lean_array_push(x_78, x_25);
x_80 = lean_array_push(x_79, x_1);
x_81 = lean_array_push(x_80, x_2);
x_82 = lean_array_push(x_81, x_26);
x_83 = lean_array_push(x_82, x_3);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_83, x_83, x_84, x_76);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_61);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_70);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_box(0);
x_62 = x_87;
goto block_69;
}
}
else
{
lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(0);
x_62 = x_88;
goto block_69;
}
block_69:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = l_Lean_indentExpr(x_63);
x_65 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__2;
x_68 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_67, x_66, x_4, x_5, x_6, x_7, x_61);
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
uint8_t x_89; 
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
x_89 = !lean_is_exclusive(x_30);
if (x_89 == 0)
{
return x_30;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_30, 0);
x_91 = lean_ctor_get(x_30, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_30);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
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
x_93 = !lean_is_exclusive(x_27);
if (x_93 == 0)
{
return x_27;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_27, 0);
x_95 = lean_ctor_get(x_27, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_27);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_11);
if (x_97 == 0)
{
return x_11;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_11, 0);
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_11);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_8);
return x_101;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = l_Lean_indentExpr(x_17);
x_19 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp___closed__5;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_22 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_21, x_20, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Expr_appFn_x21(x_12);
x_24 = l_Lean_Expr_appFn_x21(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_27 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_25);
x_28 = l___private_Lean_Meta_InferType_4__getLevelImp(x_25, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_31 = l___private_Lean_Meta_AppBuilder_7__infer(x_1, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_33, 2);
lean_inc(x_43);
lean_dec(x_33);
if (lean_obj_tag(x_43) == 7)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 3)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_29);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_50 = l_Lean_mkConst(x_49, x_48);
x_51 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_52 = lean_array_push(x_51, x_25);
x_53 = lean_array_push(x_52, x_26);
x_54 = lean_array_push(x_53, x_1);
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_array_push(x_55, x_27);
x_57 = lean_array_push(x_56, x_3);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_57, x_57, x_58, x_50);
lean_dec(x_57);
lean_ctor_set(x_31, 0, x_59);
return x_31;
}
else
{
lean_object* x_60; 
lean_dec(x_44);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
x_35 = x_60;
goto block_42;
}
}
else
{
lean_object* x_61; 
lean_dec(x_43);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_35 = x_61;
goto block_42;
}
}
else
{
lean_object* x_62; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(0);
x_35 = x_62;
goto block_42;
}
block_42:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_1);
x_37 = l_Lean_indentExpr(x_36);
x_38 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_41 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_40, x_39, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_41;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
if (lean_obj_tag(x_63) == 7)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_63, 2);
lean_inc(x_73);
lean_dec(x_63);
if (lean_obj_tag(x_73) == 7)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 3)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_29);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_80 = l_Lean_mkConst(x_79, x_78);
x_81 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__6;
x_82 = lean_array_push(x_81, x_25);
x_83 = lean_array_push(x_82, x_26);
x_84 = lean_array_push(x_83, x_1);
x_85 = lean_array_push(x_84, x_2);
x_86 = lean_array_push(x_85, x_27);
x_87 = lean_array_push(x_86, x_3);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_87, x_87, x_88, x_80);
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_64);
return x_90;
}
else
{
lean_object* x_91; 
lean_dec(x_74);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_box(0);
x_65 = x_91;
goto block_72;
}
}
else
{
lean_object* x_92; 
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
x_65 = x_92;
goto block_72;
}
}
else
{
lean_object* x_93; 
lean_dec(x_63);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_box(0);
x_65 = x_93;
goto block_72;
}
block_72:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_1);
x_67 = l_Lean_indentExpr(x_66);
x_68 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp___closed__5;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp___closed__1;
x_71 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_70, x_69, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_71;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_31);
if (x_94 == 0)
{
return x_31;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_31, 0);
x_96 = lean_ctor_get(x_31, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_31);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_28);
if (x_98 == 0)
{
return x_28;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_28, 0);
x_100 = lean_ctor_get(x_28, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_28);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_11);
if (x_102 == 0)
{
return x_11;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_11, 0);
x_104 = lean_ctor_get(x_11, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_11);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_2);
lean_ctor_set(x_106, 1, x_8);
return x_106;
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
x_19 = lean_alloc_ctor(9, 2, 0);
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
x_27 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_24, x_3, x_4, x_5, x_6, x_13);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_28);
x_39 = l_Lean_indentExpr(x_38);
x_40 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_43 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_42, x_41, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
if (lean_obj_tag(x_44) == 5)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_1);
x_46 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
x_52 = lean_name_mk_string(x_50, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_32);
x_54 = l_Lean_mkConst(x_52, x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_55);
x_57 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_56);
x_58 = lean_mk_array(x_56, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_56, x_59);
lean_dec(x_56);
x_61 = l___private_Lean_Expr_3__getAppArgsAux___main(x_28, x_58, x_60);
x_62 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_63 = lean_array_push(x_62, x_1);
x_64 = lean_array_push(x_63, x_25);
x_65 = lean_array_push(x_64, x_26);
x_66 = lean_array_push(x_65, x_2);
x_67 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_66, x_66, x_55, x_61);
lean_dec(x_66);
x_68 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_67, x_67, x_55, x_54);
lean_dec(x_67);
lean_ctor_set(x_46, 0, x_68);
return x_46;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_69 = lean_ctor_get(x_46, 0);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_46);
x_71 = lean_ctor_get(x_45, 0);
lean_inc(x_71);
lean_dec(x_45);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__1;
x_74 = lean_name_mk_string(x_72, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_32);
x_76 = l_Lean_mkConst(x_74, x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_77);
x_79 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_78);
x_80 = lean_mk_array(x_78, x_79);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_sub(x_78, x_81);
lean_dec(x_78);
x_83 = l___private_Lean_Expr_3__getAppArgsAux___main(x_28, x_80, x_82);
x_84 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_85 = lean_array_push(x_84, x_1);
x_86 = lean_array_push(x_85, x_25);
x_87 = lean_array_push(x_86, x_26);
x_88 = lean_array_push(x_87, x_2);
x_89 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_88, x_88, x_77, x_83);
lean_dec(x_88);
x_90 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_89, x_89, x_77, x_76);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_70);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_46);
if (x_92 == 0)
{
return x_46;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_46, 0);
x_94 = lean_ctor_get(x_46, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_46);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_44);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_28);
x_97 = l_Lean_indentExpr(x_96);
x_98 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_101 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_100, x_99, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_28);
x_103 = l_Lean_indentExpr(x_102);
x_104 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__2;
x_107 = l___private_Lean_Meta_AppBuilder_9__throwAppBuilderException___rarg(x_106, x_105, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_112; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_11);
if (x_112 == 0)
{
return x_11;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_11, 0);
x_114 = lean_ctor_get(x_11, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_11);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_8);
if (x_116 == 0)
{
return x_8;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_8, 0);
x_118 = lean_ctor_get(x_8, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_8);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_5);
x_13 = lean_nat_dec_lt(x_6, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_5, x_6);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_4);
x_17 = l_Lean_isSubobjectField_x3f(x_4, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_26 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_24, x_2, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_17, 0, x_28);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_17, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_17);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_6, x_33);
lean_dec(x_6);
x_6 = x_34;
x_11 = x_32;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_40 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_43 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_41, x_2, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_6, x_50);
lean_dec(x_6);
x_6 = x_51;
x_11 = x_49;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
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
x_8 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_74 = lean_alloc_ctor(9, 2, 0);
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
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__10;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_AppBuilder_8__hasTypeMsg(x_1, x_12);
x_45 = lean_alloc_ctor(9, 2, 0);
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
x_17 = lean_alloc_ctor(9, 2, 0);
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
x_13 = l_Lean_listToExpr___rarg___closed__4;
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
x_16 = l_Lean_listToExpr___rarg___closed__6;
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
x_24 = l_Lean_listToExpr___rarg___closed__4;
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
x_28 = l_Lean_listToExpr___rarg___closed__6;
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
x_14 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
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
x_22 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
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
lean_object* x_8; uint8_t x_21; lean_object* x_22; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_479 = lean_st_ref_get(x_6, x_7);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_480, 2);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_ctor_get_uint8(x_481, sizeof(void*)*1);
lean_dec(x_481);
if (x_482 == 0)
{
lean_object* x_483; uint8_t x_484; 
x_483 = lean_ctor_get(x_479, 1);
lean_inc(x_483);
lean_dec(x_479);
x_484 = 0;
x_21 = x_484;
x_22 = x_483;
goto block_478;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
x_485 = lean_ctor_get(x_479, 1);
lean_inc(x_485);
lean_dec(x_479);
x_486 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_487 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_486, x_3, x_4, x_5, x_6, x_485);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
x_490 = lean_unbox(x_488);
lean_dec(x_488);
x_21 = x_490;
x_22 = x_489;
goto block_478;
}
block_20:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
block_478:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_st_ref_get(x_6, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_6, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 2);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_35 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_35);
x_36 = lean_st_ref_set(x_6, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_71 = lean_st_ref_get(x_4, x_37);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_take(x_4, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = l_Lean_MetavarContext_incDepth(x_79);
lean_ctor_set(x_76, 0, x_80);
x_81 = lean_st_ref_set(x_4, x_76, x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_87, x_2, x_89, x_90, x_89, x_90, x_88, x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_6, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 2);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get_uint8(x_99, sizeof(void*)*1);
lean_dec(x_99);
x_101 = lean_st_ref_take(x_6, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_102, 2);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_27);
x_108 = lean_st_ref_set(x_6, x_102, x_104);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
x_111 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_111);
lean_ctor_set(x_84, 0, x_92);
lean_ctor_set(x_108, 0, x_84);
x_8 = x_108;
goto block_20;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_113);
lean_ctor_set(x_84, 0, x_92);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_84);
lean_ctor_set(x_114, 1, x_112);
x_8 = x_114;
goto block_20;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_103, 0);
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_27);
lean_ctor_set(x_102, 2, x_116);
x_117 = lean_st_ref_set(x_6, x_102, x_104);
lean_dec(x_6);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_120);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_84);
lean_ctor_set(x_121, 1, x_118);
x_8 = x_121;
goto block_20;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_102, 0);
x_123 = lean_ctor_get(x_102, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_102);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_125 = x_103;
} else {
 lean_dec_ref(x_103);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 1, 1);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_27);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_126);
x_128 = lean_st_ref_set(x_6, x_127, x_104);
lean_dec(x_6);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(x_100);
lean_ctor_set(x_84, 1, x_131);
lean_ctor_set(x_84, 0, x_92);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_84);
lean_ctor_set(x_132, 1, x_129);
x_8 = x_132;
goto block_20;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_84);
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_91, 1);
lean_inc(x_134);
lean_dec(x_91);
x_135 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_134);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_38 = x_133;
x_39 = x_136;
goto block_70;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_84, 0);
x_138 = lean_ctor_get(x_84, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_84);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_141 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_137, x_2, x_139, x_140, x_139, x_140, x_138, x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_get(x_6, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 2);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get_uint8(x_149, sizeof(void*)*1);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_6, x_148);
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
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_27);
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
x_165 = lean_box(x_150);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
x_8 = x_167;
goto block_20;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_141, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_141, 1);
lean_inc(x_169);
lean_dec(x_141);
x_170 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_169);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_38 = x_168;
x_39 = x_171;
goto block_70;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_83, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_83, 1);
lean_inc(x_173);
lean_dec(x_83);
x_174 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_173);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_38 = x_172;
x_39 = x_175;
goto block_70;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_76, 0);
x_177 = lean_ctor_get(x_76, 1);
x_178 = lean_ctor_get(x_76, 2);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_76);
x_179 = l_Lean_MetavarContext_incDepth(x_176);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
x_181 = lean_st_ref_set(x_4, x_180, x_77);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_186, x_2, x_189, x_190, x_189, x_190, x_187, x_3, x_4, x_5, x_6, x_185);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_193);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_st_ref_get(x_6, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 2);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get_uint8(x_199, sizeof(void*)*1);
lean_dec(x_199);
x_201 = lean_st_ref_take(x_6, x_198);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 1, 1);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_207)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_207;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_206);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_st_ref_set(x_6, x_211, x_204);
lean_dec(x_6);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = lean_box(x_200);
if (lean_is_scalar(x_188)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_188;
}
lean_ctor_set(x_216, 0, x_192);
lean_ctor_set(x_216, 1, x_215);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
x_8 = x_217;
goto block_20;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_188);
x_218 = lean_ctor_get(x_191, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_191, 1);
lean_inc(x_219);
lean_dec(x_191);
x_220 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_219);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_38 = x_218;
x_39 = x_221;
goto block_70;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_183, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 1);
lean_inc(x_223);
lean_dec(x_183);
x_224 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_3, x_4, x_5, x_6, x_223);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_38 = x_222;
x_39 = x_225;
goto block_70;
}
}
block_70:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_st_ref_get(x_6, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 2);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_27);
x_49 = lean_st_ref_set(x_6, x_43, x_45);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_38);
x_8 = x_49;
goto block_20;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
x_8 = x_53;
goto block_20;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_27);
lean_ctor_set(x_43, 2, x_55);
x_56 = lean_st_ref_set(x_6, x_43, x_45);
lean_dec(x_6);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_57);
x_8 = x_59;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_63 = x_44;
} else {
 lean_dec_ref(x_44);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_27);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_st_ref_set(x_6, x_65, x_45);
lean_dec(x_6);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_67);
x_8 = x_69;
goto block_20;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_226 = lean_ctor_get(x_30, 0);
lean_inc(x_226);
lean_dec(x_30);
x_227 = 0;
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_227);
lean_ctor_set(x_29, 2, x_228);
x_229 = lean_st_ref_set(x_6, x_29, x_31);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_251 = lean_st_ref_get(x_4, x_230);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_st_ref_take(x_4, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 2);
lean_inc(x_260);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_261 = x_256;
} else {
 lean_dec_ref(x_256);
 x_261 = lean_box(0);
}
x_262 = l_Lean_MetavarContext_incDepth(x_258);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 3, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
lean_ctor_set(x_263, 2, x_260);
x_264 = lean_st_ref_set(x_4, x_263, x_257);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_274 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_269, x_2, x_272, x_273, x_272, x_273, x_270, x_3, x_4, x_5, x_6, x_268);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_3, x_4, x_5, x_6, x_276);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_st_ref_get(x_6, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 2);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get_uint8(x_282, sizeof(void*)*1);
lean_dec(x_282);
x_284 = lean_st_ref_take(x_6, x_281);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_285, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 x_290 = x_285;
} else {
 lean_dec_ref(x_285);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_286, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_292 = x_286;
} else {
 lean_dec_ref(x_286);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 1, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 3, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_289);
lean_ctor_set(x_294, 2, x_293);
x_295 = lean_st_ref_set(x_6, x_294, x_287);
lean_dec(x_6);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = lean_box(x_283);
if (lean_is_scalar(x_271)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_271;
}
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_296);
x_8 = x_300;
goto block_20;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_271);
x_301 = lean_ctor_get(x_274, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_274, 1);
lean_inc(x_302);
lean_dec(x_274);
x_303 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_3, x_4, x_5, x_6, x_302);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_231 = x_301;
x_232 = x_304;
goto block_250;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_266, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_266, 1);
lean_inc(x_306);
lean_dec(x_266);
x_307 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_254, x_3, x_4, x_5, x_6, x_306);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec(x_307);
x_231 = x_305;
x_232 = x_308;
goto block_250;
}
block_250:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_233 = lean_st_ref_get(x_6, x_232);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_st_ref_take(x_6, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_237, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 1, 1);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_241)) {
 x_245 = lean_alloc_ctor(0, 3, 0);
} else {
 x_245 = x_241;
}
lean_ctor_set(x_245, 0, x_239);
lean_ctor_set(x_245, 1, x_240);
lean_ctor_set(x_245, 2, x_244);
x_246 = lean_st_ref_set(x_6, x_245, x_238);
lean_dec(x_6);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_231);
lean_ctor_set(x_249, 1, x_247);
x_8 = x_249;
goto block_20;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_309 = lean_ctor_get(x_29, 0);
x_310 = lean_ctor_get(x_29, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_29);
x_311 = lean_ctor_get(x_30, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_312 = x_30;
} else {
 lean_dec_ref(x_30);
 x_312 = lean_box(0);
}
x_313 = 0;
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 1, 1);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_315, 0, x_309);
lean_ctor_set(x_315, 1, x_310);
lean_ctor_set(x_315, 2, x_314);
x_316 = lean_st_ref_set(x_6, x_315, x_31);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_338 = lean_st_ref_get(x_4, x_317);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_st_ref_take(x_4, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 2);
lean_inc(x_347);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 x_348 = x_343;
} else {
 lean_dec_ref(x_343);
 x_348 = lean_box(0);
}
x_349 = l_Lean_MetavarContext_incDepth(x_345);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 3, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_346);
lean_ctor_set(x_350, 2, x_347);
x_351 = lean_st_ref_set(x_4, x_350, x_344);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_358 = x_354;
} else {
 lean_dec_ref(x_354);
 x_358 = lean_box(0);
}
x_359 = lean_unsigned_to_nat(0u);
x_360 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_361 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_356, x_2, x_359, x_360, x_359, x_360, x_357, x_3, x_4, x_5, x_6, x_355);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_3, x_4, x_5, x_6, x_363);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_st_ref_get(x_6, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 2);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get_uint8(x_369, sizeof(void*)*1);
lean_dec(x_369);
x_371 = lean_st_ref_take(x_6, x_368);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_372, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 x_377 = x_372;
} else {
 lean_dec_ref(x_372);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_373, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_379 = x_373;
} else {
 lean_dec_ref(x_373);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 1, 1);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_377)) {
 x_381 = lean_alloc_ctor(0, 3, 0);
} else {
 x_381 = x_377;
}
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_381, 1, x_376);
lean_ctor_set(x_381, 2, x_380);
x_382 = lean_st_ref_set(x_6, x_381, x_374);
lean_dec(x_6);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = lean_box(x_370);
if (lean_is_scalar(x_358)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_358;
}
lean_ctor_set(x_386, 0, x_362);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_384;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_383);
x_8 = x_387;
goto block_20;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_358);
x_388 = lean_ctor_get(x_361, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_361, 1);
lean_inc(x_389);
lean_dec(x_361);
x_390 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_3, x_4, x_5, x_6, x_389);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_318 = x_388;
x_319 = x_391;
goto block_337;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_353, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_353, 1);
lean_inc(x_393);
lean_dec(x_353);
x_394 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_341, x_3, x_4, x_5, x_6, x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_318 = x_392;
x_319 = x_395;
goto block_337;
}
block_337:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_320 = lean_st_ref_get(x_6, x_319);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_st_ref_take(x_6, x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_323, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 lean_ctor_release(x_323, 2);
 x_328 = x_323;
} else {
 lean_dec_ref(x_323);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_324, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_330 = x_324;
} else {
 lean_dec_ref(x_324);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 1);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_328)) {
 x_332 = lean_alloc_ctor(0, 3, 0);
} else {
 x_332 = x_328;
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_327);
lean_ctor_set(x_332, 2, x_331);
x_333 = lean_st_ref_set(x_6, x_332, x_325);
lean_dec(x_6);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
 lean_ctor_set_tag(x_336, 1);
}
lean_ctor_set(x_336, 0, x_318);
lean_ctor_set(x_336, 1, x_334);
x_8 = x_336;
goto block_20;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_396 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_6, x_22);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_408 = lean_st_ref_get(x_4, x_398);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_st_ref_take(x_4, x_410);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = !lean_is_exclusive(x_413);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_413, 0);
x_417 = l_Lean_MetavarContext_incDepth(x_416);
lean_ctor_set(x_413, 0, x_417);
x_418 = lean_st_ref_set(x_4, x_413, x_414);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_420 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
lean_dec(x_421);
x_425 = lean_unsigned_to_nat(0u);
x_426 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_427 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_423, x_2, x_425, x_426, x_425, x_426, x_424, x_3, x_4, x_5, x_6, x_422);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_429);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec(x_430);
x_432 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_433 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_432, x_3, x_4, x_5, x_6, x_431);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_434 = !lean_is_exclusive(x_433);
if (x_434 == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_433, 0);
lean_dec(x_435);
lean_ctor_set(x_433, 0, x_428);
return x_433;
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_433, 1);
lean_inc(x_436);
lean_dec(x_433);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_428);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
lean_dec(x_427);
x_440 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_439);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec(x_440);
x_399 = x_438;
x_400 = x_441;
goto block_407;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_ctor_get(x_420, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_420, 1);
lean_inc(x_443);
lean_dec(x_420);
x_444 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_443);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_399 = x_442;
x_400 = x_445;
goto block_407;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_446 = lean_ctor_get(x_413, 0);
x_447 = lean_ctor_get(x_413, 1);
x_448 = lean_ctor_get(x_413, 2);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_413);
x_449 = l_Lean_MetavarContext_incDepth(x_446);
x_450 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_447);
lean_ctor_set(x_450, 2, x_448);
x_451 = lean_st_ref_set(x_4, x_450, x_414);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_452);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_ctor_get(x_454, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_454, 1);
lean_inc(x_457);
lean_dec(x_454);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_460 = l___private_Lean_Meta_AppBuilder_19__mkAppMAux___main(x_456, x_2, x_458, x_459, x_458, x_459, x_457, x_3, x_4, x_5, x_6, x_455);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_462);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
x_465 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_466 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_465, x_3, x_4, x_5, x_6, x_464);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_461);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_460, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_460, 1);
lean_inc(x_471);
lean_dec(x_460);
x_472 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_471);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_399 = x_470;
x_400 = x_473;
goto block_407;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_474 = lean_ctor_get(x_453, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_453, 1);
lean_inc(x_475);
lean_dec(x_453);
x_476 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_411, x_3, x_4, x_5, x_6, x_475);
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
lean_dec(x_476);
x_399 = x_474;
x_400 = x_477;
goto block_407;
}
}
block_407:
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_401 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_402 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_check___spec__2(x_397, x_401, x_3, x_4, x_5, x_6, x_400);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_402, 0);
lean_dec(x_404);
lean_ctor_set_tag(x_402, 1);
lean_ctor_set(x_402, 0, x_399);
return x_402;
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_399);
lean_ctor_set(x_406, 1, x_405);
return x_406;
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
lean_dec(x_18);
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
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1___boxed), 7, 2);
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
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
