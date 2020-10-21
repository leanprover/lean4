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
lean_object* l_Lean_Meta_mkLe___rarg___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_916____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg___closed__2;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__2(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg___closed__1;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Meta_mkSorry___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2;
extern lean_object* l___private_Init_LeanInit_14__quoteList___main___rarg___closed__7;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3;
lean_object* l_Lean_Meta_mkProjection___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux_match__1(lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__3(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__2(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Array_hasQuote___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6;
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___rarg___closed__1;
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
lean_object* l_Lean_Meta_mkEqRec(lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3;
lean_object* l_Lean_Meta_mkAppM___rarg___closed__2;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
lean_object* l_Lean_Meta_mkEqOfHEq___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEqMP(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object*);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__2(lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__5(lean_object*);
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__4(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEqNDRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Meta_mkDecideProof___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__1(lean_object*);
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
lean_object* l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Meta_mkEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__2(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4;
lean_object* l_Lean_Meta_mkCongrFun___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp_match__1(lean_object*);
extern lean_object* l_Lean_getStructureCtor___closed__3;
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6;
lean_object* l_Lean_Meta_mkArrayLit(lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__1;
extern lean_object* l_Lean_MessageData_nil___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4;
extern lean_object* l_Lean_mkDecIsTrue___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__2;
lean_object* l_Lean_Meta_mkEqRefl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l_Lean_Meta_mkAppOptM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__4;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__2(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4;
lean_object* l_Lean_Meta_mkPure(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3;
lean_object* l_Lean_Meta_mkAppM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Meta_mkDecideProof___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
lean_object* l_Lean_Meta_mkProjection(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__2(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp_match__1(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm(lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___at_Lean_Meta_mkDecideProof___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__1;
lean_object* l_Lean_Meta_mkPure___rarg___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_mkArrayLit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7;
lean_object* l_Lean_Meta_mkEqTrans(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit___at_Lean_Meta_mkArrayLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM_match__1(lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
extern lean_object* l_Lean_MessageData_Lean_Message___instance__16___closed__2;
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1;
lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__4(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2;
lean_object* l_Lean_Meta_mkListLit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3;
lean_object* l_Lean_Meta_mkPure___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__2(lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__4;
lean_object* l_Lean_Meta_mkAppM___rarg___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp_match__1(lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLe___rarg___closed__3;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure___rarg___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__3(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___rarg___closed__3;
lean_object* l_Lean_Meta_mkEq(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l___private_Init_LeanInit_14__quoteList___main___rarg___closed__4;
lean_object* l_Lean_Meta_mkListLit(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt(lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2;
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
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2;
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp), 6, 1);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2;
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
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2;
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_9, x_3, x_4, x_5, x_6, x_10);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_9, x_3, x_4, x_5, x_6, x_13);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqImp), 7, 2);
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
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
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
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp), 6, 1);
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
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
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
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp), 6, 1);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_indentExpr(x_1);
x_4 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_indentExpr(x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("AppBuilder for '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_916____spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symm");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_10);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
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
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_22, x_2, x_3, x_4, x_5, x_11);
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
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2;
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
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2;
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp), 6, 1);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_9 = lean_apply_1(x_5, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_apply_6(x_3, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trans");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
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
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_13);
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
x_54 = l_Lean_Expr_isAppOfArity(x_12, x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_2);
x_55 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2;
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_58, x_57, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
else
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = l_Lean_Expr_isAppOfArity(x_15, x_52, x_53);
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
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2;
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_23, x_22, x_3, x_4, x_5, x_6, x_16);
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
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_27, x_3, x_4, x_5, x_6, x_16);
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
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2;
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
x_43 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2;
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_4(x_2, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality proof expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_10);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
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
x_27 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_23, x_2, x_3, x_4, x_5, x_11);
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
x_32 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1;
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
x_39 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1;
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
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp), 6, 1);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_apply_1(x_5, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_apply_8(x_3, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
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
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_13);
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
x_58 = l_Lean_Expr_isAppOfArity(x_12, x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_2);
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_60 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
x_63 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_62, x_61, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_63;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = l_Lean_Expr_isAppOfArity(x_15, x_56, x_57);
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
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_24, x_23, x_3, x_4, x_5, x_6, x_16);
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
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_29, x_3, x_4, x_5, x_6, x_16);
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
x_40 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
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
x_47 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_4(x_2, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eqOfHEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2;
x_17 = l_Lean_mkConst(x_16, x_15);
x_18 = l_Lean_mkApp4(x_17, x_1, x_2, x_3, x_4);
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
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2;
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = l_Lean_mkApp4(x_24, x_1, x_2, x_3, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality types are not definitionally equal");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nis not definitionally equal to");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_12 = l_Lean_Expr_isAppOfArity(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_13 = l_Lean_indentExpr(x_1);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Expr_appFn_x21(x_8);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_26 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_23);
x_27 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_23, x_25, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_indentExpr(x_23);
x_32 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_indentExpr(x_25);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2;
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_40, x_39, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_25);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1(x_23, x_24, x_26, x_1, x_47, x_2, x_3, x_4, x_5, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
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
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEqOfHEq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp), 6, 1);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_5, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_apply_5(x_3, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrArg");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non-dependent function expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_10);
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
x_93 = l_Lean_Expr_isAppOfArity(x_9, x_91, x_92);
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
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_9);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_19, x_18, x_3, x_4, x_5, x_6, x_13);
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
x_27 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_23, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_24);
x_30 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_24, x_3, x_4, x_5, x_6, x_29);
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
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
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
x_44 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
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
x_58 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
x_62 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_61, x_60, x_3, x_4, x_5, x_6, x_13);
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
x_67 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_68 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2;
x_71 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_70, x_69, x_3, x_4, x_5, x_6, x_13);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof between functions expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_9);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2;
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_17, x_16, x_3, x_4, x_5, x_6, x_10);
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
x_24 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_21, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
lean_dec(x_25);
x_30 = 0;
lean_inc(x_28);
x_31 = l_Lean_mkLambda(x_27, x_30, x_28, x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_28, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_2);
lean_inc(x_31);
x_35 = l_Lean_mkApp(x_31, x_2);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_35, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2;
x_43 = l_Lean_mkConst(x_42, x_41);
x_44 = l_Lean_mkApp6(x_43, x_28, x_31, x_22, x_23, x_1, x_2);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2;
x_51 = l_Lean_mkConst(x_50, x_49);
x_52 = l_Lean_mkApp6(x_51, x_28, x_31, x_22, x_23, x_1, x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_32);
if (x_58 == 0)
{
return x_32;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_32, 0);
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_32);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_dec(x_24);
x_63 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_9);
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2;
x_67 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_66, x_65, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_24);
if (x_68 == 0)
{
return x_24;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_24, 0);
x_70 = lean_ctor_get(x_24, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_24);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_8);
if (x_72 == 0)
{
return x_8;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_mkCongrFun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_9 = lean_apply_1(x_5, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_apply_6(x_3, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp_match__2___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_10);
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
x_80 = l_Lean_Expr_isAppOfArity(x_9, x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_2);
x_81 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_9);
x_82 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
x_85 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_84, x_83, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_85;
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = l_Lean_Expr_isAppOfArity(x_12, x_78, x_79);
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
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_13);
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
x_30 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_24, x_3, x_4, x_5, x_6, x_13);
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
x_42 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_27, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_40);
x_45 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_40, x_3, x_4, x_5, x_6, x_44);
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
x_51 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
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
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
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
x_34 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_9);
x_35 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2;
x_38 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_37, x_36, x_3, x_4, x_5, x_6, x_32);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp), 7, 2);
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
lean_object* l_Lean_Meta_synthInstance___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_12, x_18, x_3, x_4, x_5, x_6, x_19);
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
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result contains metavariables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2(x_4, x_10, x_5, x_6, x_7, x_8, x_9);
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
x_17 = l_Lean_Meta_hasAssignableMVar___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp_x3f___spec__4(x_15, x_5, x_6, x_7, x_8, x_16);
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
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_1, x_27, x_5, x_6, x_7, x_8, x_24);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 1:
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_8(x_6, x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_apply_5(x_7, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux_match__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_mkApp(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(x_1, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_indentExpr(x_9);
x_17 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_2);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_11);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_14);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_34, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppM");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit arguments provided to");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arguments");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_17 = lean_array_get_size(x_4);
x_18 = lean_expr_instantiate_rev_range(x_14, x_5, x_17, x_4);
lean_dec(x_17);
lean_dec(x_14);
x_19 = (uint8_t)((x_16 << 24) >> 61);
x_20 = lean_box(x_19);
switch (lean_obj_tag(x_20)) {
case 1:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = 0;
lean_inc(x_8);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_13, x_8, x_9, x_10, x_11, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_push(x_4, x_24);
x_4 = x_26;
x_7 = x_15;
x_12 = x_25;
goto _start;
}
case 3:
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_18);
x_29 = 1;
lean_inc(x_8);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_28, x_29, x_13, x_8, x_9, x_10, x_11, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = lean_array_push(x_4, x_31);
x_34 = l_Lean_Expr_mvarId_x21(x_31);
lean_dec(x_31);
x_35 = lean_array_push(x_6, x_34);
x_4 = x_33;
x_6 = x_35;
x_7 = x_15;
x_12 = x_32;
goto _start;
}
default: 
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_20);
lean_dec(x_13);
x_37 = lean_array_get_size(x_2);
x_38 = lean_nat_dec_lt(x_3, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_39 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2;
x_40 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_39, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_fget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_41);
x_42 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_41, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_45 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_18, x_43, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_49, x_1);
lean_dec(x_4);
x_51 = l_Lean_MessageData_nil___closed__1;
x_52 = l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___spec__1(x_50, x_41, x_51, x_8, x_9, x_10, x_11, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_3, x_54);
lean_dec(x_3);
x_56 = lean_array_push(x_4, x_41);
x_3 = x_55;
x_4 = x_56;
x_7 = x_15;
x_12 = x_53;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_41);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_array_get_size(x_4);
x_67 = lean_expr_instantiate_rev_range(x_7, x_5, x_66, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_67, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Expr_isForall(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_69);
lean_dec(x_66);
x_72 = lean_array_get_size(x_2);
x_73 = lean_nat_dec_eq(x_3, x_72);
lean_dec(x_72);
lean_dec(x_3);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_4);
x_74 = l_Lean_indentExpr(x_1);
x_75 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_MessageData_ofList___closed__3;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_83 = l_Lean_MessageData_arrayExpr_toMessageData(x_2, x_81, x_82);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2;
x_86 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_85, x_84, x_8, x_9, x_10, x_11, x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2;
x_88 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_87, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_70);
lean_dec(x_6);
lean_dec(x_4);
return x_88;
}
}
else
{
x_5 = x_66;
x_7 = x_69;
x_12 = x_70;
goto _start;
}
}
else
{
uint8_t x_90; 
lean_dec(x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_68);
if (x_90 == 0)
{
return x_68;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_68, 0);
x_92 = lean_ctor_get(x_68, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_68);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_14);
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
x_22 = l_Lean_Meta_mkFreshLevelMVar___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl___spec__1___rarg(x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_21, x_2, x_3, x_4, x_5, x_24);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAppM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkAppM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM_match__1___rarg), 2, 0);
return x_2;
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
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux(x_8, x_1, x_10, x_11, x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
if (x_3 == 0)
{
uint8_t x_209; 
x_209 = 1;
x_9 = x_209;
goto block_208;
}
else
{
uint8_t x_210; 
x_210 = 0;
x_9 = x_210;
goto block_208;
}
block_208:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__2___rarg(x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_12, x_2, x_10, x_4, x_5, x_6, x_7, x_16);
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
x_24 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_12, x_2, x_10, x_4, x_5, x_6, x_7, x_23);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_2);
x_29 = lean_st_ref_get(x_7, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
x_34 = lean_st_ref_take(x_7, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 3);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_41);
x_42 = lean_st_ref_set(x_7, x_35, x_37);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_7);
x_44 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_7, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_7, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 3);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_33);
x_56 = lean_st_ref_set(x_7, x_50, x_52);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_45);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_51, 0);
lean_inc(x_61);
lean_dec(x_51);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_33);
lean_ctor_set(x_50, 3, x_62);
x_63 = lean_st_ref_set(x_7, x_50, x_52);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
x_69 = lean_ctor_get(x_50, 2);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_71 = x_51;
} else {
 lean_dec_ref(x_51);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 1, 1);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_33);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_72);
x_74 = lean_st_ref_set(x_7, x_73, x_52);
lean_dec(x_7);
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
lean_ctor_set(x_77, 0, x_45);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_44, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_44, 1);
lean_inc(x_79);
lean_dec(x_44);
x_80 = lean_st_ref_get(x_7, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_take(x_7, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_83, 3);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_33);
x_89 = lean_st_ref_set(x_7, x_83, x_85);
lean_dec(x_7);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 0, x_78);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
lean_dec(x_84);
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_33);
lean_ctor_set(x_83, 3, x_95);
x_96 = lean_st_ref_set(x_7, x_83, x_85);
lean_dec(x_7);
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
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_78);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_83, 0);
x_101 = lean_ctor_get(x_83, 1);
x_102 = lean_ctor_get(x_83, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_83);
x_103 = lean_ctor_get(x_84, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_104 = x_84;
} else {
 lean_dec_ref(x_84);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 1, 1);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_33);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_101);
lean_ctor_set(x_106, 2, x_102);
lean_ctor_set(x_106, 3, x_105);
x_107 = lean_st_ref_set(x_7, x_106, x_85);
lean_dec(x_7);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
 lean_ctor_set_tag(x_110, 1);
}
lean_ctor_set(x_110, 0, x_78);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_36, 0);
lean_inc(x_111);
lean_dec(x_36);
x_112 = 0;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_ctor_set(x_35, 3, x_113);
x_114 = lean_st_ref_set(x_7, x_35, x_37);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
lean_inc(x_7);
x_116 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_7, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_take(x_7, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 2);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_130 = x_123;
} else {
 lean_dec_ref(x_123);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 1);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_128)) {
 x_132 = lean_alloc_ctor(0, 4, 0);
} else {
 x_132 = x_128;
}
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_126);
lean_ctor_set(x_132, 2, x_127);
lean_ctor_set(x_132, 3, x_131);
x_133 = lean_st_ref_set(x_7, x_132, x_124);
lean_dec(x_7);
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
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_117);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_116, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_116, 1);
lean_inc(x_138);
lean_dec(x_116);
x_139 = lean_st_ref_get(x_7, x_138);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_st_ref_take(x_7, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 2);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_150 = x_143;
} else {
 lean_dec_ref(x_143);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_148)) {
 x_152 = lean_alloc_ctor(0, 4, 0);
} else {
 x_152 = x_148;
}
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_146);
lean_ctor_set(x_152, 2, x_147);
lean_ctor_set(x_152, 3, x_151);
x_153 = lean_st_ref_set(x_7, x_152, x_144);
lean_dec(x_7);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_137);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_157 = lean_ctor_get(x_35, 0);
x_158 = lean_ctor_get(x_35, 1);
x_159 = lean_ctor_get(x_35, 2);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_35);
x_160 = lean_ctor_get(x_36, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_161 = x_36;
} else {
 lean_dec_ref(x_36);
 x_161 = lean_box(0);
}
x_162 = 0;
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 1, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_163);
x_165 = lean_st_ref_set(x_7, x_164, x_37);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
lean_inc(x_7);
x_167 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_st_ref_get(x_7, x_169);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_st_ref_take(x_7, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 2);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 1, 1);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_179)) {
 x_183 = lean_alloc_ctor(0, 4, 0);
} else {
 x_183 = x_179;
}
lean_ctor_set(x_183, 0, x_176);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set(x_183, 2, x_178);
lean_ctor_set(x_183, 3, x_182);
x_184 = lean_st_ref_set(x_7, x_183, x_175);
lean_dec(x_7);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_168);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_188 = lean_ctor_get(x_167, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_167, 1);
lean_inc(x_189);
lean_dec(x_167);
x_190 = lean_st_ref_get(x_7, x_189);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_st_ref_take(x_7, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_199 = x_193;
} else {
 lean_dec_ref(x_193);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_194, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_201 = x_194;
} else {
 lean_dec_ref(x_194);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 1, 1);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(0, 4, 0);
} else {
 x_203 = x_199;
}
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_197);
lean_ctor_set(x_203, 2, x_198);
lean_ctor_set(x_203, 3, x_202);
x_204 = lean_st_ref_set(x_7, x_203, x_195);
lean_dec(x_7);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_188);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appBuilder");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
x_2 = l_Lean_Meta_mkAppM___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_mkAppM___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAppM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__2___boxed), 8, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_8(x_6, x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_apply_5(x_7, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_match__4___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppOptM");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments provided to");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_expr_instantiate_rev_range(x_7, x_5, x_13, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_isForall(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_13);
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_eq(x_3, x_19);
lean_dec(x_19);
lean_dec(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_empty___closed__1;
x_23 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(x_2, x_2, x_21, x_22);
x_24 = l_Lean_indentExpr(x_1);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_MessageData_ofList___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_32 = l_Lean_MessageData_arrayExpr_toMessageData(x_23, x_21, x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_35 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_34, x_33, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_36, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_6);
lean_dec(x_4);
return x_37;
}
}
else
{
x_5 = x_13;
x_7 = x_16;
x_12 = x_17;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_get_size(x_4);
x_44 = lean_expr_instantiate_rev_range(x_7, x_5, x_43, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_45 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_44, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Expr_isForall(x_46);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_46);
lean_dec(x_43);
x_49 = lean_array_get_size(x_2);
x_50 = lean_nat_dec_eq(x_3, x_49);
lean_dec(x_49);
lean_dec(x_3);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_4);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Array_empty___closed__1;
x_53 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2(x_2, x_2, x_51, x_52);
x_54 = l_Lean_indentExpr(x_1);
x_55 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_MessageData_ofList___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_62 = l_Lean_MessageData_arrayExpr_toMessageData(x_53, x_51, x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_65 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_64, x_63, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_67 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_66, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_6);
lean_dec(x_4);
return x_67;
}
}
else
{
x_5 = x_43;
x_7 = x_46;
x_12 = x_47;
goto _start;
}
}
else
{
uint8_t x_69; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 2:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_get_size(x_4);
x_74 = lean_expr_instantiate_rev_range(x_7, x_5, x_73, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_74, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_isForall(x_76);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_76);
lean_dec(x_73);
x_79 = lean_array_get_size(x_2);
x_80 = lean_nat_dec_eq(x_3, x_79);
lean_dec(x_79);
lean_dec(x_3);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_6);
lean_dec(x_4);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Array_empty___closed__1;
x_83 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3(x_2, x_2, x_81, x_82);
x_84 = l_Lean_indentExpr(x_1);
x_85 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_MessageData_ofList___closed__3;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_92 = l_Lean_MessageData_arrayExpr_toMessageData(x_83, x_81, x_91);
lean_dec(x_83);
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_95 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_94, x_93, x_8, x_9, x_10, x_11, x_77);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_97 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_96, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_77);
lean_dec(x_6);
lean_dec(x_4);
return x_97;
}
}
else
{
x_5 = x_73;
x_7 = x_76;
x_12 = x_77;
goto _start;
}
}
else
{
uint8_t x_99; 
lean_dec(x_73);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_75);
if (x_99 == 0)
{
return x_75;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_75, 0);
x_101 = lean_ctor_get(x_75, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_75);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
case 3:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_array_get_size(x_4);
x_104 = lean_expr_instantiate_rev_range(x_7, x_5, x_103, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_105 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_104, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Expr_isForall(x_106);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
lean_dec(x_106);
lean_dec(x_103);
x_109 = lean_array_get_size(x_2);
x_110 = lean_nat_dec_eq(x_3, x_109);
lean_dec(x_109);
lean_dec(x_3);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_6);
lean_dec(x_4);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Array_empty___closed__1;
x_113 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4(x_2, x_2, x_111, x_112);
x_114 = l_Lean_indentExpr(x_1);
x_115 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_MessageData_ofList___closed__3;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_122 = l_Lean_MessageData_arrayExpr_toMessageData(x_113, x_111, x_121);
lean_dec(x_113);
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_125 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_124, x_123, x_8, x_9, x_10, x_11, x_107);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_127 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_126, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_107);
lean_dec(x_6);
lean_dec(x_4);
return x_127;
}
}
else
{
x_5 = x_103;
x_7 = x_106;
x_12 = x_107;
goto _start;
}
}
else
{
uint8_t x_129; 
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_105);
if (x_129 == 0)
{
return x_105;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_105, 0);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_105);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 4:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_array_get_size(x_4);
x_134 = lean_expr_instantiate_rev_range(x_7, x_5, x_133, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_135 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_134, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Expr_isForall(x_136);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_136);
lean_dec(x_133);
x_139 = lean_array_get_size(x_2);
x_140 = lean_nat_dec_eq(x_3, x_139);
lean_dec(x_139);
lean_dec(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_6);
lean_dec(x_4);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Array_empty___closed__1;
x_143 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5(x_2, x_2, x_141, x_142);
x_144 = l_Lean_indentExpr(x_1);
x_145 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_MessageData_ofList___closed__3;
x_148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_152 = l_Lean_MessageData_arrayExpr_toMessageData(x_143, x_141, x_151);
lean_dec(x_143);
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_155 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_154, x_153, x_8, x_9, x_10, x_11, x_137);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_157 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_156, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_137);
lean_dec(x_6);
lean_dec(x_4);
return x_157;
}
}
else
{
x_5 = x_133;
x_7 = x_136;
x_12 = x_137;
goto _start;
}
}
else
{
uint8_t x_159; 
lean_dec(x_133);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_135);
if (x_159 == 0)
{
return x_135;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_135, 0);
x_161 = lean_ctor_get(x_135, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_135);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
case 5:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_array_get_size(x_4);
x_164 = lean_expr_instantiate_rev_range(x_7, x_5, x_163, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_165 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_164, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Expr_isForall(x_166);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
lean_dec(x_166);
lean_dec(x_163);
x_169 = lean_array_get_size(x_2);
x_170 = lean_nat_dec_eq(x_3, x_169);
lean_dec(x_169);
lean_dec(x_3);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_6);
lean_dec(x_4);
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Array_empty___closed__1;
x_173 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6(x_2, x_2, x_171, x_172);
x_174 = l_Lean_indentExpr(x_1);
x_175 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_176 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = l_Lean_MessageData_ofList___closed__3;
x_178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_180 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_182 = l_Lean_MessageData_arrayExpr_toMessageData(x_173, x_171, x_181);
lean_dec(x_173);
x_183 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
x_184 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_185 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_184, x_183, x_8, x_9, x_10, x_11, x_167);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_187 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_186, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_167);
lean_dec(x_6);
lean_dec(x_4);
return x_187;
}
}
else
{
x_5 = x_163;
x_7 = x_166;
x_12 = x_167;
goto _start;
}
}
else
{
uint8_t x_189; 
lean_dec(x_163);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_165);
if (x_189 == 0)
{
return x_165;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_165, 0);
x_191 = lean_ctor_get(x_165, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_165);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 6:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_array_get_size(x_4);
x_194 = lean_expr_instantiate_rev_range(x_7, x_5, x_193, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_195 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_194, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_Expr_isForall(x_196);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_193);
x_199 = lean_array_get_size(x_2);
x_200 = lean_nat_dec_eq(x_3, x_199);
lean_dec(x_199);
lean_dec(x_3);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_6);
lean_dec(x_4);
x_201 = lean_unsigned_to_nat(0u);
x_202 = l_Array_empty___closed__1;
x_203 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7(x_2, x_2, x_201, x_202);
x_204 = l_Lean_indentExpr(x_1);
x_205 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_MessageData_ofList___closed__3;
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_212 = l_Lean_MessageData_arrayExpr_toMessageData(x_203, x_201, x_211);
lean_dec(x_203);
x_213 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_215 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_214, x_213, x_8, x_9, x_10, x_11, x_197);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_217 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_216, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_197);
lean_dec(x_6);
lean_dec(x_4);
return x_217;
}
}
else
{
x_5 = x_193;
x_7 = x_196;
x_12 = x_197;
goto _start;
}
}
else
{
uint8_t x_219; 
lean_dec(x_193);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_195);
if (x_219 == 0)
{
return x_195;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_195, 0);
x_221 = lean_ctor_get(x_195, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_195);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
case 7:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint64_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_223 = lean_ctor_get(x_7, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_7, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_7, 2);
lean_inc(x_225);
x_226 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_227 = lean_array_get_size(x_4);
x_228 = lean_expr_instantiate_rev_range(x_224, x_5, x_227, x_4);
lean_dec(x_227);
lean_dec(x_224);
x_229 = lean_array_get_size(x_2);
x_230 = lean_nat_dec_lt(x_3, x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_5);
lean_dec(x_3);
x_231 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_232 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_231, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_232;
}
else
{
lean_object* x_233; 
x_233 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; lean_object* x_235; 
x_234 = (uint8_t)((x_226 << 24) >> 61);
x_235 = lean_box(x_234);
if (lean_obj_tag(x_235) == 3)
{
lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_228);
x_237 = 1;
lean_inc(x_8);
x_238 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_236, x_237, x_223, x_8, x_9, x_10, x_11, x_12);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_3, x_241);
lean_dec(x_3);
lean_inc(x_239);
x_243 = lean_array_push(x_4, x_239);
x_244 = l_Lean_Expr_mvarId_x21(x_239);
lean_dec(x_239);
x_245 = lean_array_push(x_6, x_244);
x_3 = x_242;
x_4 = x_243;
x_6 = x_245;
x_7 = x_225;
x_12 = x_240;
goto _start;
}
else
{
lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_235);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_228);
x_248 = 0;
lean_inc(x_8);
x_249 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_247, x_248, x_223, x_8, x_9, x_10, x_11, x_12);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_add(x_3, x_252);
lean_dec(x_3);
x_254 = lean_array_push(x_4, x_250);
x_3 = x_253;
x_4 = x_254;
x_7 = x_225;
x_12 = x_251;
goto _start;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_223);
x_256 = lean_ctor_get(x_233, 0);
lean_inc(x_256);
lean_dec(x_233);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_256);
x_257 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_256, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_260 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_228, x_258, x_8, x_9, x_10, x_11, x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_unbox(x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_264, x_1);
lean_dec(x_4);
x_266 = l_Lean_MessageData_nil___closed__1;
x_267 = l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___spec__1(x_265, x_256, x_266, x_8, x_9, x_10, x_11, x_263);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_260, 1);
lean_inc(x_268);
lean_dec(x_260);
x_269 = lean_unsigned_to_nat(1u);
x_270 = lean_nat_add(x_3, x_269);
lean_dec(x_3);
x_271 = lean_array_push(x_4, x_256);
x_3 = x_270;
x_4 = x_271;
x_7 = x_225;
x_12 = x_268;
goto _start;
}
}
else
{
uint8_t x_273; 
lean_dec(x_256);
lean_dec(x_225);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_273 = !lean_is_exclusive(x_260);
if (x_273 == 0)
{
return x_260;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_260, 0);
x_275 = lean_ctor_get(x_260, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_260);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_256);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_257);
if (x_277 == 0)
{
return x_257;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_257, 0);
x_279 = lean_ctor_get(x_257, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_257);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
}
}
case 8:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_array_get_size(x_4);
x_282 = lean_expr_instantiate_rev_range(x_7, x_5, x_281, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_283 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_282, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = l_Lean_Expr_isForall(x_284);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
lean_dec(x_284);
lean_dec(x_281);
x_287 = lean_array_get_size(x_2);
x_288 = lean_nat_dec_eq(x_3, x_287);
lean_dec(x_287);
lean_dec(x_3);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_6);
lean_dec(x_4);
x_289 = lean_unsigned_to_nat(0u);
x_290 = l_Array_empty___closed__1;
x_291 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8(x_2, x_2, x_289, x_290);
x_292 = l_Lean_indentExpr(x_1);
x_293 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = l_Lean_MessageData_ofList___closed__3;
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_300 = l_Lean_MessageData_arrayExpr_toMessageData(x_291, x_289, x_299);
lean_dec(x_291);
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
x_302 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_303 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_302, x_301, x_8, x_9, x_10, x_11, x_285);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_305 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_304, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_285);
lean_dec(x_6);
lean_dec(x_4);
return x_305;
}
}
else
{
x_5 = x_281;
x_7 = x_284;
x_12 = x_285;
goto _start;
}
}
else
{
uint8_t x_307; 
lean_dec(x_281);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_283);
if (x_307 == 0)
{
return x_283;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_283, 0);
x_309 = lean_ctor_get(x_283, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_283);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
case 9:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_array_get_size(x_4);
x_312 = lean_expr_instantiate_rev_range(x_7, x_5, x_311, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_313 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_312, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lean_Expr_isForall(x_314);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_314);
lean_dec(x_311);
x_317 = lean_array_get_size(x_2);
x_318 = lean_nat_dec_eq(x_3, x_317);
lean_dec(x_317);
lean_dec(x_3);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_6);
lean_dec(x_4);
x_319 = lean_unsigned_to_nat(0u);
x_320 = l_Array_empty___closed__1;
x_321 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9(x_2, x_2, x_319, x_320);
x_322 = l_Lean_indentExpr(x_1);
x_323 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_324 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
x_325 = l_Lean_MessageData_ofList___closed__3;
x_326 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_328 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_330 = l_Lean_MessageData_arrayExpr_toMessageData(x_321, x_319, x_329);
lean_dec(x_321);
x_331 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_330);
x_332 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_333 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_332, x_331, x_8, x_9, x_10, x_11, x_315);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_335 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_334, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_315);
lean_dec(x_6);
lean_dec(x_4);
return x_335;
}
}
else
{
x_5 = x_311;
x_7 = x_314;
x_12 = x_315;
goto _start;
}
}
else
{
uint8_t x_337; 
lean_dec(x_311);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_313);
if (x_337 == 0)
{
return x_313;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_313, 0);
x_339 = lean_ctor_get(x_313, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_313);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
case 10:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_array_get_size(x_4);
x_342 = lean_expr_instantiate_rev_range(x_7, x_5, x_341, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_343 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_342, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_Expr_isForall(x_344);
if (x_346 == 0)
{
lean_object* x_347; uint8_t x_348; 
lean_dec(x_344);
lean_dec(x_341);
x_347 = lean_array_get_size(x_2);
x_348 = lean_nat_dec_eq(x_3, x_347);
lean_dec(x_347);
lean_dec(x_3);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_6);
lean_dec(x_4);
x_349 = lean_unsigned_to_nat(0u);
x_350 = l_Array_empty___closed__1;
x_351 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10(x_2, x_2, x_349, x_350);
x_352 = l_Lean_indentExpr(x_1);
x_353 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_354 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lean_MessageData_ofList___closed__3;
x_356 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_358 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_360 = l_Lean_MessageData_arrayExpr_toMessageData(x_351, x_349, x_359);
lean_dec(x_351);
x_361 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_360);
x_362 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_363 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_362, x_361, x_8, x_9, x_10, x_11, x_345);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_365 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_364, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_345);
lean_dec(x_6);
lean_dec(x_4);
return x_365;
}
}
else
{
x_5 = x_341;
x_7 = x_344;
x_12 = x_345;
goto _start;
}
}
else
{
uint8_t x_367; 
lean_dec(x_341);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_367 = !lean_is_exclusive(x_343);
if (x_367 == 0)
{
return x_343;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_343, 0);
x_369 = lean_ctor_get(x_343, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_343);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
case 11:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_array_get_size(x_4);
x_372 = lean_expr_instantiate_rev_range(x_7, x_5, x_371, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_373 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_372, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = l_Lean_Expr_isForall(x_374);
if (x_376 == 0)
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_374);
lean_dec(x_371);
x_377 = lean_array_get_size(x_2);
x_378 = lean_nat_dec_eq(x_3, x_377);
lean_dec(x_377);
lean_dec(x_3);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_6);
lean_dec(x_4);
x_379 = lean_unsigned_to_nat(0u);
x_380 = l_Array_empty___closed__1;
x_381 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11(x_2, x_2, x_379, x_380);
x_382 = l_Lean_indentExpr(x_1);
x_383 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Lean_MessageData_ofList___closed__3;
x_386 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_390 = l_Lean_MessageData_arrayExpr_toMessageData(x_381, x_379, x_389);
lean_dec(x_381);
x_391 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_390);
x_392 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_393 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_392, x_391, x_8, x_9, x_10, x_11, x_375);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_395 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_394, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_375);
lean_dec(x_6);
lean_dec(x_4);
return x_395;
}
}
else
{
x_5 = x_371;
x_7 = x_374;
x_12 = x_375;
goto _start;
}
}
else
{
uint8_t x_397; 
lean_dec(x_371);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_373);
if (x_397 == 0)
{
return x_373;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_373, 0);
x_399 = lean_ctor_get(x_373, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_373);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
default: 
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_array_get_size(x_4);
x_402 = lean_expr_instantiate_rev_range(x_7, x_5, x_401, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_402, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = l_Lean_Expr_isForall(x_404);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
lean_dec(x_404);
lean_dec(x_401);
x_407 = lean_array_get_size(x_2);
x_408 = lean_nat_dec_eq(x_3, x_407);
lean_dec(x_407);
lean_dec(x_3);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_6);
lean_dec(x_4);
x_409 = lean_unsigned_to_nat(0u);
x_410 = l_Array_empty___closed__1;
x_411 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12(x_2, x_2, x_409, x_410);
x_412 = l_Lean_indentExpr(x_1);
x_413 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_414 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
x_415 = l_Lean_MessageData_ofList___closed__3;
x_416 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8;
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l_Lean_MessageData_Lean_Message___instance__16___closed__2;
x_420 = l_Lean_MessageData_arrayExpr_toMessageData(x_411, x_409, x_419);
lean_dec(x_411);
x_421 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_420);
x_422 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_423 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_422, x_421, x_8, x_9, x_10, x_11, x_405);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; 
x_424 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_425 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_424, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_405);
lean_dec(x_6);
lean_dec(x_4);
return x_425;
}
}
else
{
x_5 = x_401;
x_7 = x_404;
x_12 = x_405;
goto _start;
}
}
else
{
uint8_t x_427; 
lean_dec(x_401);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_427 = !lean_is_exclusive(x_403);
if (x_427 == 0)
{
return x_403;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_403, 0);
x_429 = lean_ctor_get(x_403, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_403);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Meta_mkAppOptM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkAppOptM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM_match__1___rarg), 2, 0);
return x_2;
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
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_8, x_1, x_10, x_11, x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAppOptM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__2___boxed), 8, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_mkAppM___rarg___closed__4;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_10 = lean_box_uint64(x_9);
x_11 = lean_box_uint64(x_7);
x_12 = lean_apply_5(x_2, x_5, x_6, x_8, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_apply_1(x_3, x_1);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrec");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid motive");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_3, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
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
x_27 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_24, x_4, x_5, x_6, x_7, x_13);
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
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 3)
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
x_40 = l_Lean_mkConst(x_39, x_38);
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6;
x_42 = lean_array_push(x_41, x_24);
x_43 = lean_array_push(x_42, x_25);
x_44 = lean_array_push(x_43, x_1);
x_45 = lean_array_push(x_44, x_2);
x_46 = lean_array_push(x_45, x_26);
x_47 = lean_array_push(x_46, x_3);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_47, x_47, x_48, x_40);
lean_dec(x_47);
lean_ctor_set(x_30, 0, x_49);
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_dec(x_30);
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
x_56 = l_Lean_mkConst(x_55, x_54);
x_57 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6;
x_58 = lean_array_push(x_57, x_24);
x_59 = lean_array_push(x_58, x_25);
x_60 = lean_array_push(x_59, x_1);
x_61 = lean_array_push(x_60, x_2);
x_62 = lean_array_push(x_61, x_26);
x_63 = lean_array_push(x_62, x_3);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_63, x_63, x_64, x_56);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_dec(x_30);
x_68 = l_Lean_indentExpr(x_1);
x_69 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
x_72 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_71, x_70, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_dec(x_30);
x_74 = l_Lean_indentExpr(x_1);
x_75 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2;
x_78 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_77, x_76, x_4, x_5, x_6, x_7, x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_78;
}
}
else
{
uint8_t x_79; 
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
x_79 = !lean_is_exclusive(x_30);
if (x_79 == 0)
{
return x_30;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
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
x_83 = !lean_is_exclusive(x_27);
if (x_83 == 0)
{
return x_27;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_27, 0);
x_85 = lean_ctor_get(x_27, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_27);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_11);
if (x_87 == 0)
{
return x_11;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_11, 0);
x_89 = lean_ctor_get(x_11, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_11);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set(x_91, 1, x_8);
return x_91;
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp), 8, 3);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_14 = lean_box_uint64(x_13);
x_15 = lean_box_uint64(x_11);
x_16 = lean_box_uint64(x_8);
x_17 = lean_apply_8(x_2, x_6, x_7, x_9, x_10, x_12, x_14, x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_apply_1(x_3, x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_apply_1(x_3, x_1);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_apply_1(x_3, x_1);
return x_20;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_mkRecFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_indentExpr(x_3);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
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
x_27 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_24, x_4, x_5, x_6, x_7, x_13);
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
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 7)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 3)
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_41 = l_Lean_mkConst(x_40, x_39);
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6;
x_43 = lean_array_push(x_42, x_24);
x_44 = lean_array_push(x_43, x_25);
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_2);
x_47 = lean_array_push(x_46, x_26);
x_48 = lean_array_push(x_47, x_3);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_48, x_48, x_49, x_41);
lean_dec(x_48);
lean_ctor_set(x_30, 0, x_50);
return x_30;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_dec(x_30);
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_57 = l_Lean_mkConst(x_56, x_55);
x_58 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6;
x_59 = lean_array_push(x_58, x_24);
x_60 = lean_array_push(x_59, x_25);
x_61 = lean_array_push(x_60, x_1);
x_62 = lean_array_push(x_61, x_2);
x_63 = lean_array_push(x_62, x_26);
x_64 = lean_array_push(x_63, x_3);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_64, x_64, x_65, x_57);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_51);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_30, 1);
lean_inc(x_68);
lean_dec(x_30);
x_69 = l_Lean_indentExpr(x_1);
x_70 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_73 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_72, x_71, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_30, 1);
lean_inc(x_74);
lean_dec(x_30);
x_75 = l_Lean_indentExpr(x_1);
x_76 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_79 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_78, x_77, x_4, x_5, x_6, x_7, x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_30, 1);
lean_inc(x_80);
lean_dec(x_30);
x_81 = l_Lean_indentExpr(x_1);
x_82 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1;
x_85 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_84, x_83, x_4, x_5, x_6, x_7, x_80);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_85;
}
}
else
{
uint8_t x_86; 
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
x_86 = !lean_is_exclusive(x_30);
if (x_86 == 0)
{
return x_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_30, 0);
x_88 = lean_ctor_get(x_30, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_30);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
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
x_90 = !lean_is_exclusive(x_27);
if (x_90 == 0)
{
return x_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_27, 0);
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_27);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_11);
if (x_94 == 0)
{
return x_11;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_11, 0);
x_96 = lean_ctor_get(x_11, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_11);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_8);
return x_98;
}
}
}
lean_object* l_Lean_Meta_mkEqRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp), 8, 3);
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
static lean_object* _init_l_Lean_Meta_mkEqMP___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMP___rarg___closed__2() {
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
static lean_object* _init_l_Lean_Meta_mkEqMPR___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMPR___rarg___closed__2() {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noConfusion");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive type expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_13);
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
x_27 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_24, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn(x_28);
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
x_39 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2;
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_41, x_40, x_3, x_4, x_5, x_6, x_35);
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
x_45 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_1, x_3, x_4, x_5, x_6, x_35);
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
x_50 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1;
x_51 = lean_name_mk_string(x_49, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_32);
x_53 = l_Lean_mkConst(x_51, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Expr_getAppNumArgsAux(x_28, x_54);
x_56 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_57, x_59);
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
x_72 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1;
x_73 = lean_name_mk_string(x_71, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_32);
x_75 = l_Lean_mkConst(x_73, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Expr_getAppNumArgsAux(x_28, x_76);
x_78 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_77);
x_79 = lean_mk_array(x_77, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_77, x_80);
lean_dec(x_77);
x_82 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_79, x_81);
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
x_96 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2;
x_99 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_98, x_97, x_3, x_4, x_5, x_6, x_35);
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
x_101 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2;
x_104 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_103, x_102, x_3, x_4, x_5, x_6, x_29);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp), 7, 2);
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
static lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasPure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPure___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pure");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___rarg___closed__4() {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(x_1, x_23, x_7, x_8, x_9, x_10, x_11);
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
x_40 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(x_29, x_2, x_7, x_8, x_9, x_10, x_38);
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
x_46 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_39, x_7, x_8, x_9, x_10, x_45);
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
x_52 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(x_1, x_23, x_7, x_8, x_9, x_10, x_11);
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
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(x_53, x_2, x_7, x_8, x_9, x_10, x_62);
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
x_71 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_63, x_7, x_8, x_9, x_10, x_70);
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
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkProjectionn");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field name '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_getProjFnForField_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_getStructureFields(x_1, x_2);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_4);
x_16 = l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1(x_4, x_3, x_2, x_1, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_System_FilePath_dirName___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_3);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_4, x_5);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2;
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_29, x_28, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_16, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Expr_getAppNumArgsAux(x_5, x_42);
x_44 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_43);
x_45 = lean_mk_array(x_43, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_43, x_46);
lean_dec(x_43);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_45, x_47);
x_49 = l_Lean_mkConst(x_41, x_6);
x_50 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_48, x_48, x_42, x_49);
lean_dec(x_48);
x_51 = l_Lean_mkApp(x_50, x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
return x_52;
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getStructureCtor___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkProjection");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_20);
x_21 = l_Lean_isStructureLike(x_20, x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4;
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_25, x_24, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1(x_20, x_15, x_2, x_1, x_12, x_16, x_31, x_3, x_4, x_5, x_6, x_19);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_2);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_34 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2;
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_36, x_35, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
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
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Meta_mkProjection___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp), 7, 2);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_5);
x_8 = l_Lean_mkApp(x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l___private_Init_LeanInit_14__quoteList___main___rarg___closed__4;
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
x_16 = l___private_Init_LeanInit_14__quoteList___main___rarg___closed__7;
x_17 = l_Lean_mkConst(x_16, x_12);
x_18 = l_Lean_mkApp(x_17, x_1);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_15, x_18, x_2);
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
x_24 = l___private_Init_LeanInit_14__quoteList___main___rarg___closed__4;
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
x_28 = l___private_Init_LeanInit_14__quoteList___main___rarg___closed__7;
x_29 = l_Lean_mkConst(x_28, x_23);
x_30 = l_Lean_mkApp(x_29, x_1);
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_26, x_30, x_2);
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
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp), 7, 2);
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
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkArrayLit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
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
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitImp___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkArrayLit___rarg___lambda__1), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
static lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__5;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkSorry___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_218 = lean_st_ref_get(x_6, x_7);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_ctor_get_uint8(x_220, sizeof(void*)*1);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_dec(x_218);
x_223 = 0;
x_11 = x_223;
x_12 = x_222;
goto block_217;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_218, 1);
lean_inc(x_224);
lean_dec(x_218);
x_225 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_226 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_225, x_3, x_4, x_5, x_6, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unbox(x_227);
lean_dec(x_227);
x_11 = x_229;
x_12 = x_228;
goto block_217;
}
block_217:
{
uint8_t x_13; 
if (x_11 == 0)
{
uint8_t x_215; 
x_215 = 1;
x_13 = x_215;
goto block_214;
}
else
{
uint8_t x_216; 
x_216 = 0;
x_13 = x_216;
goto block_214;
}
block_214:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 3);
lean_inc(x_14);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__2___rarg(x_6, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_22 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_16, x_21, x_14, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_30 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_16, x_29, x_14, x_3, x_4, x_5, x_6, x_28);
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
lean_ctor_set(x_30, 0, x_27);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_35 = lean_st_ref_get(x_6, x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
x_40 = lean_st_ref_take(x_6, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = 0;
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_47);
x_48 = lean_st_ref_set(x_6, x_41, x_43);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_6);
x_50 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_6, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_6, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_56, 3);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_39);
x_62 = lean_st_ref_set(x_6, x_56, x_58);
lean_dec(x_6);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_51);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_57, 0);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_39);
lean_ctor_set(x_56, 3, x_68);
x_69 = lean_st_ref_set(x_6, x_56, x_58);
lean_dec(x_6);
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
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_56, 0);
x_74 = lean_ctor_get(x_56, 1);
x_75 = lean_ctor_get(x_56, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_56);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_77 = x_57;
} else {
 lean_dec_ref(x_57);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_39);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_st_ref_set(x_6, x_79, x_58);
lean_dec(x_6);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_51);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_84 = lean_ctor_get(x_50, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_50, 1);
lean_inc(x_85);
lean_dec(x_50);
x_86 = lean_st_ref_get(x_6, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_take(x_6, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_89, 3);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_39);
x_95 = lean_st_ref_set(x_6, x_89, x_91);
lean_dec(x_6);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_84);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_84);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_39);
lean_ctor_set(x_89, 3, x_101);
x_102 = lean_st_ref_set(x_6, x_89, x_91);
lean_dec(x_6);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
 lean_ctor_set_tag(x_105, 1);
}
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_106 = lean_ctor_get(x_89, 0);
x_107 = lean_ctor_get(x_89, 1);
x_108 = lean_ctor_get(x_89, 2);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_89);
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_110 = x_90;
} else {
 lean_dec_ref(x_90);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 1, 1);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_39);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_107);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_st_ref_set(x_6, x_112, x_91);
lean_dec(x_6);
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
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
 lean_ctor_set_tag(x_116, 1);
}
lean_ctor_set(x_116, 0, x_84);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_42, 0);
lean_inc(x_117);
lean_dec(x_42);
x_118 = 0;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
lean_ctor_set(x_41, 3, x_119);
x_120 = lean_st_ref_set(x_6, x_41, x_43);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_6);
x_122 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_6, x_124);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_take(x_6, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 2);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 1, 1);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_39);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 4, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_131);
lean_ctor_set(x_138, 1, x_132);
lean_ctor_set(x_138, 2, x_133);
lean_ctor_set(x_138, 3, x_137);
x_139 = lean_st_ref_set(x_6, x_138, x_130);
lean_dec(x_6);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_123);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_143 = lean_ctor_get(x_122, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_122, 1);
lean_inc(x_144);
lean_dec(x_122);
x_145 = lean_st_ref_get(x_6, x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_st_ref_take(x_6, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_148, 2);
lean_inc(x_153);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_154 = x_148;
} else {
 lean_dec_ref(x_148);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 1);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_39);
if (lean_is_scalar(x_154)) {
 x_158 = lean_alloc_ctor(0, 4, 0);
} else {
 x_158 = x_154;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_157);
x_159 = lean_st_ref_set(x_6, x_158, x_150);
lean_dec(x_6);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_143);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_163 = lean_ctor_get(x_41, 0);
x_164 = lean_ctor_get(x_41, 1);
x_165 = lean_ctor_get(x_41, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_166 = lean_ctor_get(x_42, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_167 = x_42;
} else {
 lean_dec_ref(x_42);
 x_167 = lean_box(0);
}
x_168 = 0;
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 1, 1);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_168);
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_st_ref_set(x_6, x_170, x_43);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
lean_inc(x_6);
x_173 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_st_ref_get(x_6, x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_st_ref_take(x_6, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 2);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_187 = x_180;
} else {
 lean_dec_ref(x_180);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 1, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_39);
if (lean_is_scalar(x_185)) {
 x_189 = lean_alloc_ctor(0, 4, 0);
} else {
 x_189 = x_185;
}
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_183);
lean_ctor_set(x_189, 2, x_184);
lean_ctor_set(x_189, 3, x_188);
x_190 = lean_st_ref_set(x_6, x_189, x_181);
lean_dec(x_6);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_174);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_194 = lean_ctor_get(x_173, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_173, 1);
lean_inc(x_195);
lean_dec(x_173);
x_196 = lean_st_ref_get(x_6, x_195);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_st_ref_take(x_6, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_ctor_get(x_199, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 2);
lean_inc(x_204);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_205 = x_199;
} else {
 lean_dec_ref(x_199);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 1, 1);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_39);
if (lean_is_scalar(x_205)) {
 x_209 = lean_alloc_ctor(0, 4, 0);
} else {
 x_209 = x_205;
}
lean_ctor_set(x_209, 0, x_202);
lean_ctor_set(x_209, 1, x_203);
lean_ctor_set(x_209, 2, x_204);
lean_ctor_set(x_209, 3, x_208);
x_210 = lean_st_ref_set(x_6, x_209, x_201);
lean_dec(x_6);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_194);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
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
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Meta_mkDecideProof___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Meta_mkDecideProof___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofDecideEqTrue");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2() {
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
x_8 = l_Lean_Lean_ToExpr___instance__3___lambda__1___closed__6;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
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
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_8, x_3, x_4, x_5, x_6, x_11);
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
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_13, x_10, x_3, x_4, x_5, x_6, x_14);
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
static lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decide");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_Meta_mkDecideProof___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___rarg___closed__3() {
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
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
static lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLess");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLt___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Less");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___rarg___closed__4() {
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
static lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLessEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLe___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LessEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___rarg___closed__4() {
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
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkIdImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqTransImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqSymmImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqTransImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___lambda__1___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrArgImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrFunImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkCongrImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMAux___closed__8);
l_Lean_Meta_mkAppM___rarg___closed__1 = _init_l_Lean_Meta_mkAppM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__1);
l_Lean_Meta_mkAppM___rarg___closed__2 = _init_l_Lean_Meta_mkAppM___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__2);
l_Lean_Meta_mkAppM___rarg___closed__3 = _init_l_Lean_Meta_mkAppM___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__3);
l_Lean_Meta_mkAppM___rarg___closed__4 = _init_l_Lean_Meta_mkAppM___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAppM___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp___closed__1);
l_Lean_Meta_mkEqMP___rarg___closed__1 = _init_l_Lean_Meta_mkEqMP___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMP___rarg___closed__1);
l_Lean_Meta_mkEqMP___rarg___closed__2 = _init_l_Lean_Meta_mkEqMP___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMP___rarg___closed__2);
l_Lean_Meta_mkEqMPR___rarg___closed__1 = _init_l_Lean_Meta_mkEqMPR___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___rarg___closed__1);
l_Lean_Meta_mkEqMPR___rarg___closed__2 = _init_l_Lean_Meta_mkEqMPR___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___rarg___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8);
l_Lean_Meta_mkPure___rarg___closed__1 = _init_l_Lean_Meta_mkPure___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__1);
l_Lean_Meta_mkPure___rarg___closed__2 = _init_l_Lean_Meta_mkPure___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__2);
l_Lean_Meta_mkPure___rarg___closed__3 = _init_l_Lean_Meta_mkPure___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__3);
l_Lean_Meta_mkPure___rarg___closed__4 = _init_l_Lean_Meta_mkPure___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkPure___rarg___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___lambda__1___closed__8);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkProjectionImp___closed__4);
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
