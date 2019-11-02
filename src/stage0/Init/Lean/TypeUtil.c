// Lean compiler output
// Module: Init.Lean.TypeUtil
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.AbstractMetavarContext Init.Lean.Trace Init.Lean.InductiveUtil Init.Lean.QuotUtil
#include "runtime/lean.h"
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
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1;
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_tracer___closed__1;
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta___rarg(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5;
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3;
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2;
lean_object* l___private_Init_Lean_TypeUtil_23__restoreIfFalse(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3;
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3;
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_tracer___closed__2;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(lean_object*, uint8_t, lean_object*);
lean_object* lean_level_mk_mvar(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main(lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2;
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2;
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_isLevelDefEq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1;
lean_object* l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_TypeUtil_13__strictOccursMax(lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2;
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1;
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___rarg(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5;
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv(lean_object*, lean_object*);
extern lean_object* l_unreachable_x21___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2;
lean_object* l_Lean_TypeUtil_isLevelDefEq___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6;
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Level_isSucc(lean_object*);
lean_object* l_Lean_Level_dec___main(lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
lean_object* l_Lean_TypeUtil_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3;
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4;
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
extern lean_object* l_unreachable_x21___rarg___closed__2;
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_tracer___closed__3;
uint8_t l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1;
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main(lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs___main(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___rarg(lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7;
lean_object* l_Lean_TypeUtil_tracer___closed__4;
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9;
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions___rarg(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2(lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv___rarg(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(lean_object*);
uint8_t l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_13__strictOccursMax___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_valueOpt(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases(lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_isLevelDefEq___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___main(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2;
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___rarg(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3;
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache;
extern lean_object* l_Option_get_x21___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_MkBindingException_toStr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars(lean_object*, lean_object*);
lean_object* l_Lean_TypeUtil_tracer(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1;
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_max(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_23__restoreIfFalse___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8;
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6;
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_1__getOptions___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_1__getOptions___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_2__getTraceState___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_2__getTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_2__getTraceState(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_3__getMCtx___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_3__getMCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_3__getMCtx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_4__getEnv___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_4__getEnv___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeUtil_4__getEnv___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_5__useZeta___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_5__useZeta___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TypeUtil_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 3, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* _init_l_Lean_TypeUtil_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_2__getTraceState___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_TypeUtil_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_1__getOptions___rarg___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeUtil_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TypeUtil_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TypeUtil_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_TypeUtil_tracer___closed__2;
x_2 = l_Lean_TypeUtil_tracer___closed__3;
x_3 = l_Lean_TypeUtil_tracer___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_TypeUtil_tracer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TypeUtil_tracer___closed__4;
return x_3;
}
}
lean_object* l_Lean_TypeUtil_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_TypeUtil_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_6__liftStateMCtx___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1;
x_2 = l_Lean_exprIsInhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_panicWithPos___rarg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_panicWithPos___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_panicWithPos___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_panicWithPos___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_4);
x_20 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_unreachable_x21___rarg___closed__1;
x_7 = lean_unsigned_to_nat(37u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_unreachable_x21___rarg___closed__2;
x_10 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg(x_6, x_7, x_8, x_9, x_4, x_5);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_local_ctx_find(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Option_get_x21___rarg___closed__1;
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_unsigned_to_nat(12u);
x_17 = l_Option_get_x21___rarg___closed__2;
x_18 = l_panicWithPos___at_Lean_AbstractMetavarContext_MkBindingException_toStr___spec__1(x_14, x_15, x_16, x_17);
x_19 = l_Lean_LocalDecl_valueOpt(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_4, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_2 = x_21;
x_5 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = l_Lean_LocalDecl_valueOpt(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_4, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_34);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_2);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_2);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_2 = x_34;
x_5 = x_42;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
x_45 = l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(x_5);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_1, 5);
lean_inc(x_49);
x_50 = lean_apply_2(x_49, x_47, x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_51; 
lean_free_object(x_45);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_2 = x_51;
x_5 = x_48;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
x_56 = lean_apply_2(x_55, x_53, x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_2);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_2 = x_58;
x_5 = x_54;
goto _start;
}
}
}
case 4:
{
lean_object* x_60; 
lean_dec(x_1);
x_60 = lean_apply_3(x_3, x_2, x_4, x_5);
return x_60;
}
case 5:
{
lean_object* x_61; 
lean_dec(x_1);
x_61 = lean_apply_3(x_3, x_2, x_4, x_5);
return x_61;
}
case 8:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_1);
x_62 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_4, x_5);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
lean_ctor_set(x_62, 0, x_2);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_apply_3(x_3, x_2, x_4, x_69);
return x_70;
}
}
case 10:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_dec(x_2);
x_2 = x_71;
goto _start;
}
case 11:
{
lean_object* x_73; 
lean_dec(x_1);
x_73 = lean_apply_3(x_3, x_2, x_4, x_5);
return x_73;
}
default: 
{
lean_object* x_74; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_5);
return x_74;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_7__whnfEasyCases___rarg), 5, 0);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_panicWithPos___rarg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_panicWithPos___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_panicWithPos___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_panicWithPos___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_4);
x_20 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_119; lean_object* x_120; 
x_119 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_120 = lean_box(x_119);
switch (lean_obj_tag(x_120)) {
case 2:
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_unsigned_to_nat(5u);
x_122 = lean_unsigned_to_nat(3u);
x_14 = x_121;
x_15 = x_122;
goto block_118;
}
case 3:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_unsigned_to_nat(4u);
x_124 = lean_unsigned_to_nat(3u);
x_14 = x_123;
x_15 = x_124;
goto block_118;
}
default: 
{
uint8_t x_125; 
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_expr_eqv(x_6, x_7);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_13);
return x_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_5);
lean_ctor_set(x_128, 1, x_13);
return x_128;
}
}
}
block_118:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_11);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_expr_eqv(x_6, x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_fget(x_11, x_14);
lean_inc(x_2);
lean_inc(x_12);
x_23 = lean_apply_3(x_2, x_22, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 5)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 5)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 4)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 1);
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_environment_find(x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_expr_eqv(x_6, x_7);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
x_39 = lean_box(x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_23);
lean_dec(x_5);
x_40 = l_Lean_exprIsInhabited;
x_41 = lean_array_get(x_40, x_11, x_15);
x_42 = lean_expr_mk_app(x_41, x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_14, x_43);
x_45 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_16, x_11, x_44, x_42);
lean_dec(x_16);
x_46 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_45, x_12, x_29);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_expr_eqv(x_6, x_7);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_48);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_expr_eqv(x_6, x_7);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_50);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_dec(x_24);
x_53 = lean_ctor_get(x_27, 0);
lean_inc(x_53);
lean_dec(x_27);
x_54 = lean_environment_find(x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_expr_eqv(x_6, x_7);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
if (lean_obj_tag(x_59) == 4)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
lean_dec(x_60);
x_62 = lean_box(x_61);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_5);
x_63 = l_Lean_exprIsInhabited;
x_64 = lean_array_get(x_63, x_11, x_15);
x_65 = lean_expr_mk_app(x_64, x_52);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_14, x_66);
x_68 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_16, x_11, x_67, x_65);
lean_dec(x_16);
x_69 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_68, x_12, x_51);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_62);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_expr_eqv(x_6, x_7);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_51);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_51);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_59);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_expr_eqv(x_6, x_7);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_51);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_51);
return x_77;
}
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_23);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_23, 0);
lean_dec(x_79);
x_80 = lean_expr_eqv(x_6, x_7);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_81);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_dec(x_23);
x_83 = lean_expr_eqv(x_6, x_7);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_23);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_23, 0);
lean_dec(x_88);
x_89 = lean_expr_eqv(x_6, x_7);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_90);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_23, 1);
lean_inc(x_91);
lean_dec(x_23);
x_92 = lean_expr_eqv(x_6, x_7);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_5);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_23, 0);
lean_dec(x_97);
x_98 = lean_expr_eqv(x_6, x_7);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_99);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_23, 1);
lean_inc(x_100);
lean_dec(x_23);
x_101 = lean_expr_eqv(x_6, x_7);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_100);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_23, 0);
lean_dec(x_106);
x_107 = lean_expr_eqv(x_6, x_7);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = l_Lean_Expr_updateFn___main(x_5, x_7);
lean_ctor_set(x_23, 0, x_108);
return x_23;
}
else
{
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_23, 1);
lean_inc(x_109);
lean_dec(x_23);
x_110 = lean_expr_eqv(x_6, x_7);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_5);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_23);
if (x_114 == 0)
{
return x_23;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_23, 0);
x_116 = lean_ctor_get(x_23, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_23);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg___boxed), 13, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_7);
x_9 = lean_apply_3(x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
x_12 = lean_apply_3(x_1, x_10, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_getAppFn___main(x_14);
x_17 = l_Lean_RecursorVal_getInduct(x_5);
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_expr_has_expr_mvar(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_14);
x_22 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_4, x_14, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
uint8_t x_23; 
lean_free_object(x_12);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_7);
lean_inc(x_24);
x_25 = lean_apply_3(x_2, x_24, x_7, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_4(x_3, x_14, x_26, x_7, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_free_object(x_22);
lean_dec(x_24);
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
lean_object* x_38; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_free_object(x_22);
lean_dec(x_24);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
return x_25;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_25, 0);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_25);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_49);
x_50 = lean_apply_3(x_2, x_49, x_7, x_15);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_apply_4(x_3, x_14, x_51, x_7, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_49);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
x_64 = lean_ctor_get(x_53, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_66 = x_53;
} else {
 lean_dec_ref(x_53);
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
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
x_68 = lean_ctor_get(x_50, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_70 = x_50;
} else {
 lean_dec_ref(x_50);
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
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Expr_getAppNumArgsAux___main(x_14, x_72);
x_74 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_73);
x_75 = lean_mk_array(x_73, x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_73, x_76);
lean_dec(x_73);
lean_inc(x_14);
x_78 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_14, x_75, x_77);
x_79 = lean_ctor_get(x_5, 2);
lean_inc(x_79);
lean_dec(x_5);
lean_inc(x_79);
x_80 = l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc(x_14);
x_81 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_4, x_14, x_79);
lean_dec(x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_81);
return x_12;
}
else
{
uint8_t x_82; 
lean_free_object(x_12);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_7);
lean_inc(x_83);
x_84 = lean_apply_3(x_2, x_83, x_7, x_15);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_apply_4(x_3, x_14, x_85, x_7, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
uint8_t x_90; 
lean_free_object(x_81);
lean_dec(x_83);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_87, 0);
lean_dec(x_97);
lean_ctor_set(x_87, 0, x_81);
return x_87;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_81);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_81);
lean_dec(x_83);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
return x_87;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_87, 0);
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_87);
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
lean_free_object(x_81);
lean_dec(x_83);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_84);
if (x_104 == 0)
{
return x_84;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_84, 0);
x_106 = lean_ctor_get(x_84, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_84);
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
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
lean_dec(x_81);
lean_inc(x_7);
lean_inc(x_108);
x_109 = lean_apply_3(x_2, x_108, x_7, x_15);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_apply_4(x_3, x_14, x_110, x_7, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_108);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_108);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_108);
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_125 = x_112;
} else {
 lean_dec_ref(x_112);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
x_127 = lean_ctor_get(x_109, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_109, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_129 = x_109;
} else {
 lean_dec_ref(x_109);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_79);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_box(0);
lean_ctor_set(x_12, 0, x_131);
return x_12;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_12, 0);
x_133 = lean_ctor_get(x_12, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_12);
x_134 = l_Lean_Expr_getAppFn___main(x_132);
x_135 = l_Lean_RecursorVal_getInduct(x_5);
x_136 = l_Lean_Expr_isConstOf(x_134, x_135);
lean_dec(x_135);
lean_dec(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
else
{
uint8_t x_139; 
x_139 = lean_expr_has_expr_mvar(x_132);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_5, 2);
lean_inc(x_140);
lean_dec(x_5);
lean_inc(x_132);
x_141 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_4, x_132, x_140);
lean_dec(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_133);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_143);
x_145 = lean_apply_3(x_2, x_143, x_7, x_133);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_apply_4(x_3, x_132, x_146, x_7, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_144);
lean_dec(x_143);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_156 = x_148;
} else {
 lean_dec_ref(x_148);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_144;
}
lean_ctor_set(x_157, 0, x_143);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_144);
lean_dec(x_143);
x_159 = lean_ctor_get(x_148, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_161 = x_148;
} else {
 lean_dec_ref(x_148);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_3);
x_163 = lean_ctor_get(x_145, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_145, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_165 = x_145;
} else {
 lean_dec_ref(x_145);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Expr_getAppNumArgsAux___main(x_132, x_167);
x_169 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_168);
x_170 = lean_mk_array(x_168, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_168, x_171);
lean_dec(x_168);
lean_inc(x_132);
x_173 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_132, x_170, x_172);
x_174 = lean_ctor_get(x_5, 2);
lean_inc(x_174);
lean_dec(x_5);
lean_inc(x_174);
x_175 = l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(x_173, x_174);
lean_dec(x_173);
if (x_175 == 0)
{
lean_object* x_176; 
lean_inc(x_132);
x_176 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_4, x_132, x_174);
lean_dec(x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_133);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_178);
x_180 = lean_apply_3(x_2, x_178, x_7, x_133);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_apply_4(x_3, x_132, x_181, x_7, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_179);
lean_dec(x_178);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_179;
}
lean_ctor_set(x_192, 0, x_178);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_179);
lean_dec(x_178);
x_194 = lean_ctor_get(x_183, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_196 = x_183;
} else {
 lean_dec_ref(x_183);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_3);
x_198 = lean_ctor_get(x_180, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_180, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_200 = x_180;
} else {
 lean_dec_ref(x_180);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_174);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_133);
return x_203;
}
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_204 = !lean_is_exclusive(x_12);
if (x_204 == 0)
{
return x_12;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_12, 0);
x_206 = lean_ctor_get(x_12, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_12);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_9);
if (x_208 == 0)
{
return x_9;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_9, 0);
x_210 = lean_ctor_get(x_9, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_9);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_RecursorVal_getMajorIdx(x_9);
x_15 = lean_array_get_size(x_11);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_expr_eqv(x_6, x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fget(x_11, x_14);
lean_inc(x_2);
lean_inc(x_12);
x_22 = lean_apply_3(x_2, x_21, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_67; 
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
x_67 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_25);
lean_dec(x_8);
x_68 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(x_23);
lean_inc(x_9);
x_69 = l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(x_9, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_68);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_expr_eqv(x_6, x_7);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_24);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_24);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux___main(x_68, x_75);
x_77 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
x_81 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_68, x_78, x_80);
x_82 = l_List_lengthAux___main___rarg(x_10, x_75);
x_83 = lean_ctor_get(x_9, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_List_lengthAux___main___rarg(x_84, x_75);
x_86 = lean_nat_dec_eq(x_82, x_85);
lean_dec(x_85);
lean_dec(x_82);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_expr_eqv(x_6, x_7);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Expr_updateFn___main(x_5, x_7);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_24);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_24);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_5);
x_91 = lean_ctor_get(x_74, 2);
lean_inc(x_91);
x_92 = lean_instantiate_lparams(x_91, x_84, x_10);
x_93 = lean_ctor_get(x_9, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_9, 4);
lean_inc(x_94);
x_95 = lean_nat_add(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
x_96 = lean_ctor_get(x_9, 5);
lean_inc(x_96);
lean_dec(x_9);
x_97 = lean_nat_add(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
x_98 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_97, x_11, x_75, x_92);
lean_dec(x_97);
x_99 = lean_array_get_size(x_81);
x_100 = lean_ctor_get(x_74, 1);
lean_inc(x_100);
lean_dec(x_74);
x_101 = lean_nat_sub(x_99, x_100);
lean_dec(x_100);
x_102 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_99, x_81, x_101, x_98);
lean_dec(x_81);
lean_dec(x_99);
x_103 = lean_nat_add(x_14, x_79);
lean_dec(x_14);
x_104 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_15, x_11, x_103, x_102);
lean_dec(x_15);
x_105 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_104, x_12, x_24);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_inc(x_12);
lean_inc(x_23);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_106 = l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__4___rarg(x_2, x_3, x_4, x_8, x_9, x_23, x_12, x_24);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_26 = x_23;
x_27 = x_108;
goto block_66;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_23);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_26 = x_110;
x_27 = x_109;
goto block_66;
}
}
else
{
uint8_t x_111; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_106);
if (x_111 == 0)
{
return x_106;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_106);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
block_66:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(x_26);
lean_inc(x_9);
x_29 = l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(x_9, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_expr_eqv(x_6, x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_updateFn___main(x_5, x_7);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; 
if (lean_is_scalar(x_25)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_25;
}
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_35);
x_37 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_28, x_38, x_40);
x_42 = l_List_lengthAux___main___rarg(x_10, x_35);
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_List_lengthAux___main___rarg(x_44, x_35);
x_46 = lean_nat_dec_eq(x_42, x_45);
lean_dec(x_45);
lean_dec(x_42);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_expr_eqv(x_6, x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_Expr_updateFn___main(x_5, x_7);
if (lean_is_scalar(x_25)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_25;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_27);
return x_49;
}
else
{
lean_object* x_50; 
if (lean_is_scalar(x_25)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_25;
}
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_27);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_25);
lean_dec(x_5);
x_51 = lean_ctor_get(x_34, 2);
lean_inc(x_51);
x_52 = lean_instantiate_lparams(x_51, x_44, x_10);
x_53 = lean_ctor_get(x_9, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_9, 4);
lean_inc(x_54);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = lean_ctor_get(x_9, 5);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_nat_add(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
x_58 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_57, x_11, x_35, x_52);
lean_dec(x_57);
x_59 = lean_array_get_size(x_41);
x_60 = lean_ctor_get(x_34, 1);
lean_inc(x_60);
lean_dec(x_34);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_60);
x_62 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_59, x_41, x_61, x_58);
lean_dec(x_41);
lean_dec(x_59);
x_63 = lean_nat_add(x_14, x_39);
lean_dec(x_14);
x_64 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_15, x_11, x_63, x_62);
lean_dec(x_15);
x_65 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_64, x_12, x_27);
return x_65;
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
return x_22;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_22, 0);
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_22);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg___boxed), 13, 0);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_panicWithPos___rarg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_panicWithPos___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_panicWithPos___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_panicWithPos___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_4);
x_20 = l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_unreachable_x21___rarg___closed__1;
x_9 = lean_unsigned_to_nat(37u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_unreachable_x21___rarg___closed__2;
x_12 = l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg(x_8, x_9, x_10, x_11, x_6, x_7);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_local_ctx_find(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Option_get_x21___rarg___closed__1;
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_unsigned_to_nat(12u);
x_19 = l_Option_get_x21___rarg___closed__2;
x_20 = l_panicWithPos___at_Lean_AbstractMetavarContext_MkBindingException_toStr___spec__1(x_16, x_17, x_18, x_19);
x_21 = l_Lean_LocalDecl_valueOpt(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_6, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
lean_ctor_set(x_24, 0, x_5);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_5);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_5 = x_23;
x_7 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = l_Lean_LocalDecl_valueOpt(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_6, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
lean_ctor_set(x_37, 0, x_5);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_5);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_5 = x_36;
x_7 = x_44;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
x_47 = l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(x_7);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_ctor_get(x_1, 5);
lean_inc(x_51);
x_52 = lean_apply_2(x_51, x_49, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_47, 0, x_5);
return x_47;
}
else
{
lean_object* x_53; 
lean_free_object(x_47);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_5 = x_53;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_ctor_get(x_1, 5);
lean_inc(x_57);
x_58 = lean_apply_2(x_57, x_55, x_46);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_5);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_5 = x_60;
x_7 = x_56;
goto _start;
}
}
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
x_63 = l_Lean_Expr_getAppFn___main(x_62);
lean_dec(x_62);
lean_inc(x_6);
lean_inc(x_63);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_64 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_63, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_isLambda(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l___private_Init_Lean_TypeUtil_4__getEnv___rarg(x_6, x_66);
if (lean_obj_tag(x_65) == 4)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_70);
x_74 = lean_environment_find(x_70, x_72);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_76);
return x_68;
}
else
{
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_5);
return x_68;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
switch (lean_obj_tag(x_77)) {
case 4:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_68);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_79);
x_81 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_80);
x_82 = lean_mk_array(x_80, x_81);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_sub(x_80, x_83);
lean_dec(x_80);
lean_inc(x_5);
x_85 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_82, x_84);
x_86 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_63, x_65, x_70, x_78, x_73, x_85, x_6, x_71);
lean_dec(x_85);
lean_dec(x_73);
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_63);
return x_86;
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_68);
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_88);
x_90 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_89);
x_91 = lean_mk_array(x_89, x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_89, x_92);
lean_dec(x_89);
lean_inc(x_5);
x_94 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_91, x_93);
x_95 = l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_63, x_65, x_70, x_87, x_73, x_94, x_6, x_71);
lean_dec(x_94);
lean_dec(x_65);
lean_dec(x_63);
return x_95;
}
default: 
{
uint8_t x_96; 
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_97);
return x_68;
}
else
{
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_5);
return x_68;
}
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_68, 0);
x_99 = lean_ctor_get(x_68, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_68);
x_100 = lean_ctor_get(x_65, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_65, 1);
lean_inc(x_101);
lean_inc(x_98);
x_102 = lean_environment_find(x_98, x_100);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
return x_105;
}
else
{
lean_object* x_106; 
lean_dec(x_65);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_5);
lean_ctor_set(x_106, 1, x_99);
return x_106;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
switch (lean_obj_tag(x_107)) {
case 4:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_109);
x_111 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_110);
x_112 = lean_mk_array(x_110, x_111);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_sub(x_110, x_113);
lean_dec(x_110);
lean_inc(x_5);
x_115 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_112, x_114);
x_116 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_63, x_65, x_98, x_108, x_101, x_115, x_6, x_99);
lean_dec(x_115);
lean_dec(x_101);
lean_dec(x_108);
lean_dec(x_65);
lean_dec(x_63);
return x_116;
}
case 7:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
lean_dec(x_107);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_118);
x_120 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_119);
x_121 = lean_mk_array(x_119, x_120);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_sub(x_119, x_122);
lean_dec(x_119);
lean_inc(x_5);
x_124 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_121, x_123);
x_125 = l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_63, x_65, x_98, x_117, x_101, x_124, x_6, x_99);
lean_dec(x_124);
lean_dec(x_65);
lean_dec(x_63);
return x_125;
}
default: 
{
uint8_t x_126; 
lean_dec(x_107);
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_99);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec(x_65);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_5);
lean_ctor_set(x_129, 1, x_99);
return x_129;
}
}
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_68);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_68, 0);
lean_dec(x_131);
x_132 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_133);
return x_68;
}
else
{
lean_dec(x_65);
lean_ctor_set(x_68, 0, x_5);
return x_68;
}
}
else
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_68, 1);
lean_inc(x_134);
lean_dec(x_68);
x_135 = lean_expr_eqv(x_63, x_65);
lean_dec(x_63);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_Expr_updateFn___main(x_5, x_65);
lean_dec(x_65);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_65);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_65);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_139);
x_141 = lean_mk_empty_array_with_capacity(x_140);
lean_dec(x_140);
x_142 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_141);
x_143 = l_Lean_Expr_betaRev(x_63, x_142);
lean_dec(x_63);
x_5 = x_143;
x_7 = x_66;
goto _start;
}
}
else
{
uint8_t x_145; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_64);
if (x_145 == 0)
{
return x_64;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_64, 0);
x_147 = lean_ctor_get(x_64, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_64);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
case 8:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_5, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_5, 3);
lean_inc(x_150);
x_151 = l___private_Init_Lean_TypeUtil_5__useZeta___rarg(x_6, x_7);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
uint8_t x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_151);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_151, 0);
lean_dec(x_155);
lean_ctor_set(x_151, 0, x_5);
return x_151;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_5);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_5);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
lean_dec(x_151);
x_159 = lean_expr_instantiate1(x_150, x_149);
lean_dec(x_149);
lean_dec(x_150);
x_5 = x_159;
x_7 = x_158;
goto _start;
}
}
case 10:
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_5, 1);
lean_inc(x_161);
lean_dec(x_5);
x_5 = x_161;
goto _start;
}
case 11:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = lean_ctor_get(x_5, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_5, 2);
lean_inc(x_164);
lean_inc(x_6);
x_165 = lean_apply_3(x_2, x_164, x_6, x_7);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l___private_Init_Lean_TypeUtil_4__getEnv___rarg(x_6, x_167);
lean_dec(x_6);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = l_Lean_Expr_getAppFn___main(x_166);
if (lean_obj_tag(x_171) == 4)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_environment_find(x_170, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_dec(x_166);
lean_dec(x_163);
lean_ctor_set(x_168, 0, x_5);
return x_168;
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
if (lean_obj_tag(x_174) == 6)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_ctor_get(x_175, 3);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_nat_add(x_176, x_163);
lean_dec(x_163);
lean_dec(x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Lean_Expr_getAppNumArgsAux___main(x_166, x_178);
x_180 = lean_nat_sub(x_179, x_177);
lean_dec(x_177);
lean_dec(x_179);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_sub(x_180, x_181);
lean_dec(x_180);
x_183 = l_Lean_Expr_getRevArgD___main(x_166, x_182, x_5);
lean_dec(x_5);
lean_dec(x_166);
lean_ctor_set(x_168, 0, x_183);
return x_168;
}
else
{
lean_dec(x_174);
lean_dec(x_166);
lean_dec(x_163);
lean_ctor_set(x_168, 0, x_5);
return x_168;
}
}
}
else
{
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_163);
lean_ctor_set(x_168, 0, x_5);
return x_168;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_168, 0);
x_185 = lean_ctor_get(x_168, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_168);
x_186 = l_Lean_Expr_getAppFn___main(x_166);
if (lean_obj_tag(x_186) == 4)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_environment_find(x_184, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
lean_dec(x_166);
lean_dec(x_163);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_5);
lean_ctor_set(x_189, 1, x_185);
return x_189;
}
else
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
if (lean_obj_tag(x_190) == 6)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_ctor_get(x_191, 3);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_nat_add(x_192, x_163);
lean_dec(x_163);
lean_dec(x_192);
x_194 = lean_unsigned_to_nat(0u);
x_195 = l_Lean_Expr_getAppNumArgsAux___main(x_166, x_194);
x_196 = lean_nat_sub(x_195, x_193);
lean_dec(x_193);
lean_dec(x_195);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_sub(x_196, x_197);
lean_dec(x_196);
x_199 = l_Lean_Expr_getRevArgD___main(x_166, x_198, x_5);
lean_dec(x_5);
lean_dec(x_166);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
lean_object* x_201; 
lean_dec(x_190);
lean_dec(x_166);
lean_dec(x_163);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_5);
lean_ctor_set(x_201, 1, x_185);
return x_201;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_166);
lean_dec(x_163);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_5);
lean_ctor_set(x_202, 1, x_185);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
x_203 = !lean_is_exclusive(x_165);
if (x_203 == 0)
{
return x_165;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_165, 0);
x_205 = lean_ctor_get(x_165, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_165);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
default: 
{
lean_object* x_207; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_5);
lean_ctor_set(x_207, 1, x_7);
return x_207;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_8__whnfCore___main___rarg), 7, 0);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_reduceRecAux___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___at___private_Init_Lean_TypeUtil_8__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_8__whnfCore___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_8__whnfCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Lean_TypeUtil_8__whnfCore___rarg(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_16 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_apply_3(x_6, x_8, x_2, x_3);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_17 = lean_apply_3(x_6, x_12, x_2, x_3);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_10__assignLevel___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_10__assignLevel___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = lean_level_mk_mvar(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_name_mk_numeral(x_12, x_13);
x_15 = lean_level_mk_mvar(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_13, x_16);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_1, 2, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_1);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_20);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
lean_inc(x_26);
lean_inc(x_25);
x_28 = lean_name_mk_numeral(x_25, x_26);
x_29 = lean_level_mk_mvar(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_26, x_30);
lean_dec(x_26);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set(x_33, 4, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___rarg), 1, 0);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
x_3 = x_13;
goto block_7;
}
block_7:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = lean_level_eq(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_occurs___main(x_1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_TypeUtil_13__strictOccursMax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Init_Lean_TypeUtil_12__strictOccursMaxAux___main(x_1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_13__strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_TypeUtil_13__strictOccursMax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(x_1, x_4, x_3);
x_2 = x_5;
x_3 = x_6;
goto _start;
}
case 5:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_name_dec_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_level_mk_max(x_3, x_2);
return x_10;
}
else
{
lean_dec(x_2);
return x_3;
}
}
default: 
{
lean_object* x_11; 
x_11 = lean_level_mk_max(x_3, x_2);
return x_11;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l___private_Init_Lean_TypeUtil_11__mkFreshLevelMVar___rarg(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_TypeUtil_14__mkMaxArgsDiff___main(x_2, x_3, x_7);
x_10 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_2, x_9, x_4, x_8);
return x_10;
}
}
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*2 + 1, x_4);
x_10 = lean_array_push(x_8, x_9);
lean_ctor_set(x_6, 4, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_4);
x_19 = lean_array_push(x_17, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_1, x_7, x_3, x_8, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_array_push(x_8, x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
lean_ctor_set(x_4, 3, x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 4);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_25 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_array_push(x_26, x_28);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 1, 1);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_25);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_24);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type_context");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level_is_def_eq");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2;
x_2 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_383; 
if (lean_obj_tag(x_4) == 1)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_4, 0);
lean_inc(x_411);
lean_dec(x_4);
x_412 = lean_ctor_get(x_5, 0);
lean_inc(x_412);
lean_dec(x_5);
x_4 = x_411;
x_5 = x_412;
goto _start;
}
else
{
lean_object* x_414; 
x_414 = lean_box(0);
x_383 = x_414;
goto block_410;
}
}
else
{
lean_object* x_415; 
x_415 = lean_box(0);
x_383 = x_415;
goto block_410;
}
block_382:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg(x_1, x_4, x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Level_normalize___main(x_10);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_1);
x_13 = l___private_Init_Lean_TypeUtil_9__instantiateLevelMVars___rarg(x_1, x_5, x_6, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Level_normalize___main(x_15);
lean_dec(x_15);
x_18 = lean_level_eq(x_4, x_12);
if (x_18 == 0)
{
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = lean_level_eq(x_5, x_17);
if (x_20 == 0)
{
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_85; lean_object* x_175; 
lean_dec(x_17);
lean_dec(x_12);
x_22 = l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(x_16);
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
if (x_2 == 0)
{
if (x_3 == 0)
{
uint8_t x_196; lean_object* x_197; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_196 = 0;
x_197 = lean_box(x_196);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_197);
return x_13;
}
else
{
uint8_t x_198; 
lean_inc(x_5);
lean_inc(x_23);
lean_inc(x_1);
x_198 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_23, x_5);
if (x_198 == 0)
{
uint8_t x_199; lean_object* x_200; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_199 = 0;
x_200 = lean_box(x_199);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_200);
return x_13;
}
else
{
lean_object* x_201; 
lean_free_object(x_13);
x_201 = lean_box(0);
x_175 = x_201;
goto block_195;
}
}
}
else
{
uint8_t x_202; 
lean_inc(x_4);
lean_inc(x_23);
lean_inc(x_1);
x_202 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_23, x_4);
if (x_202 == 0)
{
if (x_3 == 0)
{
uint8_t x_203; lean_object* x_204; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = 0;
x_204 = lean_box(x_203);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_204);
return x_13;
}
else
{
uint8_t x_205; 
lean_inc(x_5);
lean_inc(x_23);
lean_inc(x_1);
x_205 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_23, x_5);
if (x_205 == 0)
{
uint8_t x_206; lean_object* x_207; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_206 = 0;
x_207 = lean_box(x_206);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_207);
return x_13;
}
else
{
lean_object* x_208; 
lean_free_object(x_13);
x_208 = lean_box(0);
x_175 = x_208;
goto block_195;
}
}
}
else
{
lean_object* x_209; 
lean_free_object(x_13);
x_209 = lean_box(0);
x_175 = x_209;
goto block_195;
}
}
block_84:
{
uint8_t x_27; 
lean_dec(x_26);
x_27 = l_Lean_Level_isSucc(x_4);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Level_isSucc(x_5);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_29 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = 1;
x_33 = lean_box(x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Level_dec___main(x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_1);
x_39 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_24);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l_Lean_Level_dec___main(x_5);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
lean_dec(x_1);
x_50 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_24);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
x_56 = 1;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_5);
lean_dec(x_4);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_4 = x_48;
x_5 = x_59;
x_7 = x_24;
goto _start;
}
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Level_dec___main(x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_1);
x_62 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_24);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = 1;
x_66 = lean_box(x_65);
lean_ctor_set(x_62, 0, x_66);
return x_62;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = 1;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
lean_dec(x_61);
x_72 = l_Lean_Level_dec___main(x_5);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_71);
lean_dec(x_1);
x_73 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_24);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = 1;
x_77 = lean_box(x_76);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = 1;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_ctor_get(x_72, 0);
lean_inc(x_82);
lean_dec(x_72);
x_4 = x_71;
x_5 = x_82;
x_7 = x_24;
goto _start;
}
}
}
}
block_174:
{
uint8_t x_86; lean_object* x_87; lean_object* x_133; 
lean_dec(x_85);
x_86 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
if (x_86 == 0)
{
lean_object* x_154; 
x_154 = lean_box(0);
x_133 = x_154;
goto block_153;
}
else
{
if (x_2 == 0)
{
lean_object* x_155; 
x_155 = lean_box(0);
x_133 = x_155;
goto block_153;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_Level_isMVar(x_4);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_box(0);
x_133 = x_157;
goto block_153;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = l_Lean_Level_mvarId_x21(x_4);
lean_inc(x_159);
lean_inc(x_23);
x_160 = lean_apply_2(x_158, x_23, x_159);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l___private_Init_Lean_TypeUtil_13__strictOccursMax(x_4, x_5);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_4);
x_163 = l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(x_1, x_159, x_5, x_6, x_24);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
x_166 = 1;
x_167 = lean_box(x_166);
lean_ctor_set(x_163, 0, x_167);
return x_163;
}
else
{
lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = 1;
x_170 = lean_box(x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
}
else
{
lean_object* x_172; 
lean_dec(x_159);
x_172 = lean_box(0);
x_133 = x_172;
goto block_153;
}
}
else
{
lean_object* x_173; 
lean_dec(x_159);
x_173 = lean_box(0);
x_133 = x_173;
goto block_153;
}
}
}
}
block_132:
{
lean_dec(x_87);
if (x_86 == 0)
{
uint8_t x_88; 
lean_dec(x_23);
x_88 = l_Lean_Level_isMVar(x_4);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Level_isMVar(x_5);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_25);
x_90 = lean_box(0);
x_26 = x_90;
goto block_84;
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = 0;
x_92 = lean_box(x_91);
if (lean_is_scalar(x_25)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_25;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_24);
return x_93;
}
}
else
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = 0;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_25)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_25;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_24);
return x_96;
}
}
else
{
if (x_3 == 0)
{
uint8_t x_97; 
lean_dec(x_23);
x_97 = l_Lean_Level_isMVar(x_4);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Level_isMVar(x_5);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_25);
x_99 = lean_box(0);
x_26 = x_99;
goto block_84;
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = 0;
x_101 = lean_box(x_100);
if (lean_is_scalar(x_25)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_25;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_24);
return x_102;
}
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_25)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_25;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_24);
return x_105;
}
}
else
{
uint8_t x_106; 
x_106 = l_Lean_Level_isMVar(x_5);
if (x_106 == 0)
{
uint8_t x_107; 
lean_dec(x_23);
x_107 = l_Lean_Level_isMVar(x_4);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_25);
x_108 = lean_box(0);
x_26 = x_108;
goto block_84;
}
else
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_109 = 0;
x_110 = lean_box(x_109);
if (lean_is_scalar(x_25)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_25;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_24);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
x_113 = l_Lean_Level_mvarId_x21(x_5);
lean_inc(x_113);
x_114 = lean_apply_2(x_112, x_23, x_113);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l___private_Init_Lean_TypeUtil_13__strictOccursMax(x_5, x_4);
lean_dec(x_5);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
lean_dec(x_25);
x_117 = l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(x_1, x_113, x_4, x_6, x_24);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
x_120 = 1;
x_121 = lean_box(x_120);
lean_ctor_set(x_117, 0, x_121);
return x_117;
}
else
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_dec(x_117);
x_123 = 1;
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_113);
lean_dec(x_4);
lean_dec(x_1);
x_126 = 0;
x_127 = lean_box(x_126);
if (lean_is_scalar(x_25)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_25;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_24);
return x_128;
}
}
else
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_129 = 0;
x_130 = lean_box(x_129);
if (lean_is_scalar(x_25)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_25;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_24);
return x_131;
}
}
}
}
}
block_153:
{
lean_dec(x_133);
if (x_3 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_87 = x_134;
goto block_132;
}
else
{
uint8_t x_135; 
x_135 = l_Lean_Level_isMVar(x_5);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_87 = x_136;
goto block_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = l_Lean_Level_mvarId_x21(x_5);
lean_inc(x_138);
lean_inc(x_23);
x_139 = lean_apply_2(x_137, x_23, x_138);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Level_occurs___main(x_5, x_4);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
x_142 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_138, x_4, x_6, x_24);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
x_145 = 1;
x_146 = lean_box(x_145);
lean_ctor_set(x_142, 0, x_146);
return x_142;
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
return x_150;
}
}
else
{
lean_object* x_151; 
lean_dec(x_138);
x_151 = lean_box(0);
x_87 = x_151;
goto block_132;
}
}
else
{
lean_object* x_152; 
lean_dec(x_138);
x_152 = lean_box(0);
x_87 = x_152;
goto block_132;
}
}
}
}
}
block_195:
{
lean_dec(x_175);
if (x_2 == 0)
{
lean_object* x_176; 
x_176 = lean_box(0);
x_85 = x_176;
goto block_174;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_Level_isMVar(x_4);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_box(0);
x_85 = x_178;
goto block_174;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
x_180 = l_Lean_Level_mvarId_x21(x_4);
lean_inc(x_180);
lean_inc(x_23);
x_181 = lean_apply_2(x_179, x_23, x_180);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = l_Lean_Level_occurs___main(x_4, x_5);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_4);
x_184 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_180, x_5, x_6, x_24);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = 1;
x_188 = lean_box(x_187);
lean_ctor_set(x_184, 0, x_188);
return x_184;
}
else
{
lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = 1;
x_191 = lean_box(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_189);
return x_192;
}
}
else
{
lean_object* x_193; 
lean_dec(x_180);
x_193 = lean_box(0);
x_85 = x_193;
goto block_174;
}
}
else
{
lean_object* x_194; 
lean_dec(x_180);
x_194 = lean_box(0);
x_85 = x_194;
goto block_174;
}
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_13, 0);
x_211 = lean_ctor_get(x_13, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_13);
x_212 = l_Lean_Level_normalize___main(x_210);
lean_dec(x_210);
x_213 = lean_level_eq(x_4, x_12);
if (x_213 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_212;
x_7 = x_211;
goto _start;
}
else
{
uint8_t x_215; 
x_215 = lean_level_eq(x_5, x_212);
if (x_215 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_212;
x_7 = x_211;
goto _start;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_265; lean_object* x_346; 
lean_dec(x_212);
lean_dec(x_12);
x_217 = l___private_Init_Lean_TypeUtil_3__getMCtx___rarg(x_211);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
if (x_2 == 0)
{
if (x_3 == 0)
{
uint8_t x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_364 = 0;
x_365 = lean_box(x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_219);
return x_366;
}
else
{
uint8_t x_367; 
lean_inc(x_5);
lean_inc(x_218);
lean_inc(x_1);
x_367 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_218, x_5);
if (x_367 == 0)
{
uint8_t x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_368 = 0;
x_369 = lean_box(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_219);
return x_370;
}
else
{
lean_object* x_371; 
x_371 = lean_box(0);
x_346 = x_371;
goto block_363;
}
}
}
else
{
uint8_t x_372; 
lean_inc(x_4);
lean_inc(x_218);
lean_inc(x_1);
x_372 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_218, x_4);
if (x_372 == 0)
{
if (x_3 == 0)
{
uint8_t x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_373 = 0;
x_374 = lean_box(x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_219);
return x_375;
}
else
{
uint8_t x_376; 
lean_inc(x_5);
lean_inc(x_218);
lean_inc(x_1);
x_376 = l_Lean_AbstractMetavarContext_hasAssignableLevelMVar___main___rarg(x_1, x_218, x_5);
if (x_376 == 0)
{
uint8_t x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_377 = 0;
x_378 = lean_box(x_377);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_219);
return x_379;
}
else
{
lean_object* x_380; 
x_380 = lean_box(0);
x_346 = x_380;
goto block_363;
}
}
}
else
{
lean_object* x_381; 
x_381 = lean_box(0);
x_346 = x_381;
goto block_363;
}
}
block_264:
{
uint8_t x_222; 
lean_dec(x_221);
x_222 = l_Lean_Level_isSucc(x_4);
if (x_222 == 0)
{
uint8_t x_223; 
x_223 = l_Lean_Level_isSucc(x_5);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_1);
x_224 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_219);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = 1;
x_228 = lean_box(x_227);
if (lean_is_scalar(x_226)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_226;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_225);
return x_229;
}
else
{
lean_object* x_230; 
x_230 = l_Lean_Level_dec___main(x_4);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_1);
x_231 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_219);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = 1;
x_235 = lean_box(x_234);
if (lean_is_scalar(x_233)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_233;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_232);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
lean_dec(x_230);
x_238 = l_Lean_Level_dec___main(x_5);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_237);
lean_dec(x_1);
x_239 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_219);
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
x_242 = 1;
x_243 = lean_box(x_242);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_240);
return x_244;
}
else
{
lean_object* x_245; 
lean_dec(x_5);
lean_dec(x_4);
x_245 = lean_ctor_get(x_238, 0);
lean_inc(x_245);
lean_dec(x_238);
x_4 = x_237;
x_5 = x_245;
x_7 = x_219;
goto _start;
}
}
}
}
else
{
lean_object* x_247; 
x_247 = l_Lean_Level_dec___main(x_4);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_1);
x_248 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_219);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = 1;
x_252 = lean_box(x_251);
if (lean_is_scalar(x_250)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_250;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_249);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_247, 0);
lean_inc(x_254);
lean_dec(x_247);
x_255 = l_Lean_Level_dec___main(x_5);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_254);
lean_dec(x_1);
x_256 = l___private_Init_Lean_TypeUtil_16__postponeIsLevelDefEq___rarg(x_4, x_2, x_5, x_3, x_6, x_219);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = 1;
x_260 = lean_box(x_259);
if (lean_is_scalar(x_258)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_258;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_257);
return x_261;
}
else
{
lean_object* x_262; 
lean_dec(x_5);
lean_dec(x_4);
x_262 = lean_ctor_get(x_255, 0);
lean_inc(x_262);
lean_dec(x_255);
x_4 = x_254;
x_5 = x_262;
x_7 = x_219;
goto _start;
}
}
}
}
block_345:
{
uint8_t x_266; lean_object* x_267; lean_object* x_310; 
lean_dec(x_265);
x_266 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
if (x_266 == 0)
{
lean_object* x_328; 
x_328 = lean_box(0);
x_310 = x_328;
goto block_327;
}
else
{
if (x_2 == 0)
{
lean_object* x_329; 
x_329 = lean_box(0);
x_310 = x_329;
goto block_327;
}
else
{
uint8_t x_330; 
x_330 = l_Lean_Level_isMVar(x_4);
if (x_330 == 0)
{
lean_object* x_331; 
x_331 = lean_box(0);
x_310 = x_331;
goto block_327;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_332 = lean_ctor_get(x_1, 1);
lean_inc(x_332);
x_333 = l_Lean_Level_mvarId_x21(x_4);
lean_inc(x_333);
lean_inc(x_218);
x_334 = lean_apply_2(x_332, x_218, x_333);
x_335 = lean_unbox(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
uint8_t x_336; 
x_336 = l___private_Init_Lean_TypeUtil_13__strictOccursMax(x_4, x_5);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_4);
x_337 = l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(x_1, x_333, x_5, x_6, x_219);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
x_340 = 1;
x_341 = lean_box(x_340);
if (lean_is_scalar(x_339)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_339;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_338);
return x_342;
}
else
{
lean_object* x_343; 
lean_dec(x_333);
x_343 = lean_box(0);
x_310 = x_343;
goto block_327;
}
}
else
{
lean_object* x_344; 
lean_dec(x_333);
x_344 = lean_box(0);
x_310 = x_344;
goto block_327;
}
}
}
}
block_309:
{
lean_dec(x_267);
if (x_266 == 0)
{
uint8_t x_268; 
lean_dec(x_218);
x_268 = l_Lean_Level_isMVar(x_4);
if (x_268 == 0)
{
uint8_t x_269; 
x_269 = l_Lean_Level_isMVar(x_5);
if (x_269 == 0)
{
lean_object* x_270; 
lean_dec(x_220);
x_270 = lean_box(0);
x_221 = x_270;
goto block_264;
}
else
{
uint8_t x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_271 = 0;
x_272 = lean_box(x_271);
if (lean_is_scalar(x_220)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_220;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_219);
return x_273;
}
}
else
{
uint8_t x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_274 = 0;
x_275 = lean_box(x_274);
if (lean_is_scalar(x_220)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_220;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_219);
return x_276;
}
}
else
{
if (x_3 == 0)
{
uint8_t x_277; 
lean_dec(x_218);
x_277 = l_Lean_Level_isMVar(x_4);
if (x_277 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Level_isMVar(x_5);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_220);
x_279 = lean_box(0);
x_221 = x_279;
goto block_264;
}
else
{
uint8_t x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_280 = 0;
x_281 = lean_box(x_280);
if (lean_is_scalar(x_220)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_220;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_219);
return x_282;
}
}
else
{
uint8_t x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_283 = 0;
x_284 = lean_box(x_283);
if (lean_is_scalar(x_220)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_220;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_219);
return x_285;
}
}
else
{
uint8_t x_286; 
x_286 = l_Lean_Level_isMVar(x_5);
if (x_286 == 0)
{
uint8_t x_287; 
lean_dec(x_218);
x_287 = l_Lean_Level_isMVar(x_4);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_220);
x_288 = lean_box(0);
x_221 = x_288;
goto block_264;
}
else
{
uint8_t x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_289 = 0;
x_290 = lean_box(x_289);
if (lean_is_scalar(x_220)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_220;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_219);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_292 = lean_ctor_get(x_1, 1);
lean_inc(x_292);
x_293 = l_Lean_Level_mvarId_x21(x_5);
lean_inc(x_293);
x_294 = lean_apply_2(x_292, x_218, x_293);
x_295 = lean_unbox(x_294);
lean_dec(x_294);
if (x_295 == 0)
{
uint8_t x_296; 
x_296 = l___private_Init_Lean_TypeUtil_13__strictOccursMax(x_5, x_4);
lean_dec(x_5);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_220);
x_297 = l___private_Init_Lean_TypeUtil_15__solveSelfMax___rarg(x_1, x_293, x_4, x_6, x_219);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
x_300 = 1;
x_301 = lean_box(x_300);
if (lean_is_scalar(x_299)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_299;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_298);
return x_302;
}
else
{
uint8_t x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_293);
lean_dec(x_4);
lean_dec(x_1);
x_303 = 0;
x_304 = lean_box(x_303);
if (lean_is_scalar(x_220)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_220;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_219);
return x_305;
}
}
else
{
uint8_t x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_293);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_306 = 0;
x_307 = lean_box(x_306);
if (lean_is_scalar(x_220)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_220;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_219);
return x_308;
}
}
}
}
}
block_327:
{
lean_dec(x_310);
if (x_3 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_267 = x_311;
goto block_309;
}
else
{
uint8_t x_312; 
x_312 = l_Lean_Level_isMVar(x_5);
if (x_312 == 0)
{
lean_object* x_313; 
x_313 = lean_box(0);
x_267 = x_313;
goto block_309;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = lean_ctor_get(x_1, 1);
lean_inc(x_314);
x_315 = l_Lean_Level_mvarId_x21(x_5);
lean_inc(x_315);
lean_inc(x_218);
x_316 = lean_apply_2(x_314, x_218, x_315);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
if (x_317 == 0)
{
uint8_t x_318; 
x_318 = l_Lean_Level_occurs___main(x_5, x_4);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_5);
x_319 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_315, x_4, x_6, x_219);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_321 = x_319;
} else {
 lean_dec_ref(x_319);
 x_321 = lean_box(0);
}
x_322 = 1;
x_323 = lean_box(x_322);
if (lean_is_scalar(x_321)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_321;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_320);
return x_324;
}
else
{
lean_object* x_325; 
lean_dec(x_315);
x_325 = lean_box(0);
x_267 = x_325;
goto block_309;
}
}
else
{
lean_object* x_326; 
lean_dec(x_315);
x_326 = lean_box(0);
x_267 = x_326;
goto block_309;
}
}
}
}
}
block_363:
{
lean_dec(x_346);
if (x_2 == 0)
{
lean_object* x_347; 
x_347 = lean_box(0);
x_265 = x_347;
goto block_345;
}
else
{
uint8_t x_348; 
x_348 = l_Lean_Level_isMVar(x_4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_box(0);
x_265 = x_349;
goto block_345;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_350 = lean_ctor_get(x_1, 1);
lean_inc(x_350);
x_351 = l_Lean_Level_mvarId_x21(x_4);
lean_inc(x_351);
lean_inc(x_218);
x_352 = lean_apply_2(x_350, x_218, x_351);
x_353 = lean_unbox(x_352);
lean_dec(x_352);
if (x_353 == 0)
{
uint8_t x_354; 
x_354 = l_Lean_Level_occurs___main(x_4, x_5);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_4);
x_355 = l___private_Init_Lean_TypeUtil_10__assignLevel___rarg(x_1, x_351, x_5, x_6, x_219);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
x_358 = 1;
x_359 = lean_box(x_358);
if (lean_is_scalar(x_357)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_357;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_356);
return x_360;
}
else
{
lean_object* x_361; 
lean_dec(x_351);
x_361 = lean_box(0);
x_265 = x_361;
goto block_345;
}
}
else
{
lean_object* x_362; 
lean_dec(x_351);
x_362 = lean_box(0);
x_265 = x_362;
goto block_345;
}
}
}
}
}
}
}
}
block_410:
{
uint8_t x_384; 
lean_dec(x_383);
x_384 = lean_level_eq(x_4, x_5);
if (x_384 == 0)
{
uint8_t x_385; lean_object* x_386; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_7);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get_uint8(x_397, sizeof(void*)*1);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = 0;
x_385 = x_400;
x_386 = x_399;
goto block_395;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_401 = lean_ctor_get(x_396, 1);
lean_inc(x_401);
lean_dec(x_396);
x_402 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_403 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg(x_402, x_6, x_401);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_unbox(x_404);
lean_dec(x_404);
x_385 = x_406;
x_386 = x_405;
goto block_395;
}
block_395:
{
if (x_385 == 0)
{
x_8 = x_386;
goto block_382;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_inc(x_4);
x_387 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_387, 0, x_4);
x_388 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7;
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
lean_inc(x_5);
x_390 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_390, 0, x_5);
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_393 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg(x_392, x_391, x_6, x_386);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_8 = x_394;
goto block_382;
}
}
}
else
{
uint8_t x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_407 = 1;
x_408 = lean_box(x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_7);
return x_409;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___rarg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = lean_array_get_size(x_2);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_18__getNumPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_18__getNumPostponed(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Array_empty___closed__1;
lean_ctor_set(x_1, 4, x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = l_Array_empty___closed__1;
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_19__getResetPostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_19__getResetPostponed(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 0;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_18 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_1);
x_21 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(x_1, x_17, x_18, x_19, x_20, x_6, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_4 = x_14;
x_5 = x_24;
x_7 = x_23;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 3);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = l_Array_empty___closed__1;
lean_ctor_set(x_4, 0, x_13);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_3, 3, x_16);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get(x_3, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_23 = l_Array_empty___closed__1;
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 1);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_21);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 4);
lean_inc(x_31);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_32 = x_3;
} else {
 lean_dec_ref(x_3);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_34 = x_4;
} else {
 lean_dec_ref(x_4);
 x_34 = lean_box(0);
}
x_35 = l_Array_empty___closed__1;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 0;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_18 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_1);
x_21 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(x_1, x_17, x_18, x_19, x_20, x_6, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_4 = x_14;
x_5 = x_24;
x_7 = x_23;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postponed_step");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_2 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_3);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_119, sizeof(void*)*1);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = 0;
x_4 = x_122;
x_5 = x_121;
goto block_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3;
x_125 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg(x_124, x_2, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_4 = x_128;
x_5 = x_127;
goto block_117;
}
block_117:
{
if (x_4 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = 1;
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_9);
x_10 = l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(x_1, x_11, x_11, x_13, x_9, x_2, x_12);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 0;
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_22);
return x_14;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_ctor_set(x_15, 3, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
x_28 = lean_ctor_get(x_15, 2);
x_29 = lean_ctor_get(x_15, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_31 = x_16;
} else {
 lean_dec_ref(x_16);
 x_31 = lean_box(0);
}
x_32 = 0;
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_14, 1, x_34);
return x_14;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_ctor_get(x_15, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_15, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 x_40 = x_15;
} else {
 lean_dec_ref(x_15);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_42 = x_16;
} else {
 lean_dec_ref(x_16);
 x_42 = lean_box(0);
}
x_43 = 0;
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 1);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_47 = lean_ctor_get(x_7, 0);
lean_inc(x_47);
lean_dec(x_7);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_ctor_set(x_5, 3, x_49);
x_50 = l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(x_1, x_51, x_51, x_53, x_48, x_2, x_52);
lean_dec(x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 4);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = 0;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_62);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_70 = lean_ctor_get(x_5, 3);
x_71 = lean_ctor_get(x_5, 0);
x_72 = lean_ctor_get(x_5, 1);
x_73 = lean_ctor_get(x_5, 2);
x_74 = lean_ctor_get(x_5, 4);
lean_inc(x_74);
lean_inc(x_70);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_5);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_72);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_74);
x_80 = l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(x_1, x_81, x_81, x_83, x_77, x_2, x_82);
lean_dec(x_81);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_88 = x_84;
} else {
 lean_dec_ref(x_84);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 4);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
x_96 = 0;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 1, 1);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_91);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_92);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_100 = l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___rarg(x_5);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l___private_Init_Lean_TypeUtil_19__getResetPostponed___rarg(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(0u);
x_107 = 1;
x_108 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg(x_1, x_104, x_104, x_106, x_107, x_2, x_105);
lean_dec(x_104);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2;
x_112 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg(x_101, x_111, x_2, x_110);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
lean_ctor_set(x_112, 0, x_109);
return x_112;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_iterateMAux___main___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__3___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__7___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_20__processPostponedStep___spec__8___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_array_push(x_8, x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
lean_ctor_set(x_4, 3, x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 4);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_25 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_array_push(x_26, x_28);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 1, 1);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_25);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_24);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_array_push(x_8, x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
lean_ctor_set(x_4, 3, x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 4);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_25 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_array_push(x_26, x_28);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 1, 1);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_25);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_24);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no progress solving pending is-def-eq level constraints");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processing #");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" postponed is-def-eq level constraints");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_92; lean_object* x_93; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_free_object(x_5);
x_105 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_8);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_106, sizeof(void*)*1);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = 0;
x_92 = x_109;
x_93 = x_108;
goto block_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_112 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg(x_111, x_3, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_92 = x_115;
x_93 = x_114;
goto block_104;
}
block_91:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_nat_dec_eq(x_22, x_9);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_20);
x_25 = lean_nat_dec_lt(x_22, x_7);
lean_dec(x_7);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_26 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(x_2);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_37 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(x_36, x_3, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = lean_box(x_2);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_box(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_48 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3;
x_49 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(x_47, x_48, x_3, x_46);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(x_2);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
else
{
x_4 = x_23;
goto _start;
}
}
else
{
uint8_t x_57; lean_object* x_58; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_1);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_20, 0, x_58);
return x_20;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_20, 0);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_20);
x_61 = lean_nat_dec_eq(x_59, x_9);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = lean_nat_dec_lt(x_59, x_7);
lean_dec(x_7);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_1);
x_63 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_box(x_2);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_72 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(x_71, x_3, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_box(x_2);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_81 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3;
x_82 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(x_80, x_81, x_3, x_79);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_box(x_2);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
else
{
x_4 = x_60;
goto _start;
}
}
else
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_1);
x_88 = 1;
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_60);
return x_90;
}
}
}
}
block_104:
{
if (x_92 == 0)
{
x_11 = x_93;
goto block_91;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_inc(x_7);
x_94 = l_Nat_repr(x_7);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_102 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg(x_101, x_100, x_3, x_93);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_11 = x_103;
goto block_91;
}
}
}
else
{
uint8_t x_116; lean_object* x_117; 
lean_dec(x_7);
lean_dec(x_1);
x_116 = 1;
x_117 = lean_box(x_116);
lean_ctor_set(x_5, 0, x_117);
return x_5;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_5, 0);
x_119 = lean_ctor_get(x_5, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_5);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_dec_eq(x_118, x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_165; lean_object* x_166; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_119);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_179, sizeof(void*)*1);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = 0;
x_165 = x_182;
x_166 = x_181;
goto block_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
lean_dec(x_178);
x_184 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_185 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg(x_184, x_3, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_unbox(x_186);
lean_dec(x_186);
x_165 = x_188;
x_166 = x_187;
goto block_177;
}
block_164:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_inc(x_1);
x_123 = l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg(x_1, x_3, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_118);
lean_dec(x_1);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_124);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_dec(x_123);
x_130 = l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(x_129);
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
x_134 = lean_nat_dec_eq(x_131, x_120);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_133);
x_135 = lean_nat_dec_lt(x_131, x_118);
lean_dec(x_118);
lean_dec(x_131);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_1);
x_136 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_132);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_137, sizeof(void*)*1);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
x_141 = lean_box(x_2);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_dec(x_136);
x_144 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8;
x_145 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(x_144, x_3, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = lean_box(x_2);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_dec(x_145);
x_153 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_154 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3;
x_155 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(x_153, x_154, x_3, x_152);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_box(x_2);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
}
else
{
x_4 = x_132;
goto _start;
}
}
else
{
uint8_t x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_131);
lean_dec(x_118);
lean_dec(x_1);
x_161 = 1;
x_162 = lean_box(x_161);
if (lean_is_scalar(x_133)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_133;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_132);
return x_163;
}
}
}
block_177:
{
if (x_165 == 0)
{
x_122 = x_166;
goto block_164;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_118);
x_167 = l_Nat_repr(x_118);
x_168 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6;
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_175 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg(x_174, x_173, x_3, x_166);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_122 = x_176;
goto block_164;
}
}
}
else
{
uint8_t x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_118);
lean_dec(x_1);
x_189 = 1;
x_190 = lean_box(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_119);
return x_191;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_3__addTrace___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_21__processPostponedAux___main___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 3);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = l_Array_empty___closed__1;
lean_ctor_set(x_4, 0, x_13);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_3, 3, x_16);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get(x_3, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_23 = l_Array_empty___closed__1;
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 1);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_21);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 4);
lean_inc(x_31);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_32 = x_3;
} else {
 lean_dec_ref(x_3);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_34 = x_4;
} else {
 lean_dec_ref(x_4);
 x_34 = lean_box(0);
}
x_35 = l_Array_empty___closed__1;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set(x_4, 3, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_1, x_31);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_TypeUtil_1__getOptions___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postponed");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4;
x_2 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Init_Lean_TypeUtil_18__getNumPostponed___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_free_object(x_5);
x_108 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_8);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*1);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = 0;
x_11 = x_112;
x_12 = x_111;
goto block_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3;
x_115 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg(x_114, x_3, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unbox(x_116);
lean_dec(x_116);
x_11 = x_118;
x_12 = x_117;
goto block_107;
}
block_107:
{
if (x_11 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = 1;
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_16);
x_17 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 3);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_25);
return x_17;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
lean_ctor_set(x_18, 3, x_28);
return x_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_34 = x_19;
} else {
 lean_dec_ref(x_19);
 x_34 = lean_box(0);
}
x_35 = 0;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_17, 1, x_37);
return x_17;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_ctor_get(x_18, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 4);
lean_inc(x_42);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_43 = x_18;
} else {
 lean_dec_ref(x_18);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_45 = x_19;
} else {
 lean_dec_ref(x_19);
 x_45 = lean_box(0);
}
x_46 = 0;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 1, 1);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
lean_ctor_set(x_12, 3, x_52);
x_53 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 4);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
x_65 = 0;
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 1, 1);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
if (lean_is_scalar(x_62)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_62;
}
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_61);
if (lean_is_scalar(x_57)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_57;
}
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_69 = lean_ctor_get(x_12, 3);
x_70 = lean_ctor_get(x_12, 0);
x_71 = lean_ctor_get(x_12, 1);
x_72 = lean_ctor_get(x_12, 2);
x_73 = lean_ctor_get(x_12, 4);
lean_inc(x_73);
lean_inc(x_69);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_12);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = 1;
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_73);
x_79 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 4);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_90 = x_81;
} else {
 lean_dec_ref(x_81);
 x_90 = lean_box(0);
}
x_91 = 0;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_87);
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_82);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___rarg(x_12);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2;
x_102 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg(x_96, x_101, x_3, x_100);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_99);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_119; lean_object* x_120; 
lean_dec(x_1);
x_119 = 1;
x_120 = lean_box(x_119);
lean_ctor_set(x_5, 0, x_120);
return x_5;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_nat_dec_eq(x_121, x_123);
lean_dec(x_121);
if (x_124 == 0)
{
uint8_t x_125; lean_object* x_126; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = l___private_Init_Lean_TypeUtil_2__getTraceState___rarg(x_122);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_167, sizeof(void*)*1);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = 0;
x_125 = x_170;
x_126 = x_169;
goto block_165;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3;
x_173 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg(x_172, x_3, x_171);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unbox(x_174);
lean_dec(x_174);
x_125 = x_176;
x_126 = x_175;
goto block_165;
}
block_165:
{
if (x_125 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_127 = lean_ctor_get(x_126, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 4);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
x_135 = 1;
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 1, 1);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_130);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set(x_137, 4, x_131);
x_138 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_137);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_139, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_139, 4);
lean_inc(x_146);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 lean_ctor_release(x_139, 4);
 x_147 = x_139;
} else {
 lean_dec_ref(x_139);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_149 = x_140;
} else {
 lean_dec_ref(x_140);
 x_149 = lean_box(0);
}
x_150 = 0;
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_147;
}
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_145);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set(x_152, 4, x_146);
if (lean_is_scalar(x_142)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_142;
}
lean_ctor_set(x_153, 0, x_141);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___rarg(x_126);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg(x_1, x_2, x_3, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2;
x_161 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg(x_155, x_160, x_3, x_159);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_1);
x_177 = 1;
x_178 = lean_box(x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_122);
return x_179;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_2__getResetTraces___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Trace_1__addNode___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___at___private_Init_Lean_TypeUtil_22__processPostponed___spec__5___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_TypeUtil_23__restoreIfFalse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 4);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set(x_10, 0, x_4);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_5);
lean_ctor_set(x_6, 1, x_18);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_6, 1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set(x_31, 4, x_5);
lean_ctor_set(x_31, 0, x_4);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 2);
x_37 = lean_ctor_get(x_31, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_5);
lean_ctor_set(x_6, 1, x_38);
return x_6;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 3);
lean_inc(x_43);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 x_44 = x_39;
} else {
 lean_dec_ref(x_39);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_5);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Init_Lean_TypeUtil_23__restoreIfFalse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeUtil_23__restoreIfFalse___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_TypeUtil_isLevelDefEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_1);
x_10 = l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg(x_1, x_9, x_9, x_2, x_3, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 4, x_8);
lean_ctor_set(x_14, 0, x_7);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 2);
x_23 = lean_ctor_get(x_14, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_8);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 5, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_8);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = l___private_Init_Lean_TypeUtil_22__processPostponed___rarg(x_1, x_4, x_5, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 4);
lean_dec(x_44);
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
lean_ctor_set(x_41, 4, x_8);
lean_ctor_set(x_41, 0, x_7);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
x_47 = lean_ctor_get(x_41, 2);
x_48 = lean_ctor_get(x_41, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_8);
lean_ctor_set(x_37, 1, x_49);
return x_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_53);
lean_ctor_set(x_55, 4, x_8);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_37, 0);
lean_dec(x_58);
return x_37;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_38);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* l_Lean_TypeUtil_isLevelDefEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_TypeUtil_isLevelDefEq___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_TypeUtil_isLevelDefEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_TypeUtil_isLevelDefEq___rarg(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1;
x_2 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_typeContextNoCacheIsAbstractTCCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_typeContextNoCacheIsAbstractTCCache___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_AbstractMetavarContext(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
lean_object* initialize_Init_Lean_InductiveUtil(lean_object*);
lean_object* initialize_Init_Lean_QuotUtil(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeUtil(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_AbstractMetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_InductiveUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_QuotUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TypeUtil_tracer___closed__1 = _init_l_Lean_TypeUtil_tracer___closed__1();
lean_mark_persistent(l_Lean_TypeUtil_tracer___closed__1);
l_Lean_TypeUtil_tracer___closed__2 = _init_l_Lean_TypeUtil_tracer___closed__2();
lean_mark_persistent(l_Lean_TypeUtil_tracer___closed__2);
l_Lean_TypeUtil_tracer___closed__3 = _init_l_Lean_TypeUtil_tracer___closed__3();
lean_mark_persistent(l_Lean_TypeUtil_tracer___closed__3);
l_Lean_TypeUtil_tracer___closed__4 = _init_l_Lean_TypeUtil_tracer___closed__4();
lean_mark_persistent(l_Lean_TypeUtil_tracer___closed__4);
l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1 = _init_l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__1);
l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2 = _init_l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_TypeUtil_7__whnfEasyCases___main___spec__1___rarg___closed__2);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__1);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__2);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__3);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__4);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__5);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__6);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__7);
l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8 = _init_l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_17__isLevelDefEqAux___main___rarg___closed__8);
l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1 = _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__1);
l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2 = _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__2);
l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3 = _init_l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_20__processPostponedStep___rarg___closed__3);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__1);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__2);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__3);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__4);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__5);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__6);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__7);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__8);
l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9 = _init_l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_21__processPostponedAux___main___rarg___closed__9);
l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1 = _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__1);
l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2 = _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__2);
l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3 = _init_l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_TypeUtil_22__processPostponed___rarg___closed__3);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__1);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__2);
l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3 = _init_l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache___closed__3);
l_Lean_typeContextNoCacheIsAbstractTCCache = _init_l_Lean_typeContextNoCacheIsAbstractTCCache();
lean_mark_persistent(l_Lean_typeContextNoCacheIsAbstractTCCache);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
