// Lean compiler output
// Module: Lean.Meta.Injective
// Imports: Init Lean.Meta.Transform Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Assumption
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6;
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object*);
extern lean_object* l_Lean_profiler;
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_genInjectivity;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8;
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4;
double l_Lean_trace_profiler_threshold_getSecs(lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__5;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1;
static double l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2;
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1;
static lean_object* l_Lean_Meta_elimOptParam___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7;
static lean_object* l_Lean_Meta_elimOptParam___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4;
static lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1;
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_elimOptParam___lambda__1___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3;
lean_object* l_Lean_MVarId_casesAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157_(lean_object*);
lean_object* l_Lean_Meta_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_elimOptParam___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MVarId_substEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2;
static lean_object* l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6;
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2;
static lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_elimOptParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_withInstImplicitAsImplict___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3;
LEAN_EXPORT lean_object* l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_withInstImplicitAsImplict___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_uget(x_6, x_3);
x_8 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3;
x_9 = l_Lean_mkAppB(x_8, x_7, x_4);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = l_Array_back___rarg(x_3, x_1);
x_5 = l_Array_reverse___rarg(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Array_toSubarray___rarg(x_5, x_7, x_6);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1(x_8, x_10, x_12, x_4);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_elimOptParam___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optParam", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_elimOptParam___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_elimOptParam___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_elimOptParam___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Meta_elimOptParam___lambda__1___closed__2;
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Meta_elimOptParam___lambda__1___closed__3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = lean_nat_sub(x_11, x_10);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_Expr_getRevArg_x21(x_1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Meta_elimOptParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_elimOptParam___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Meta_elimOptParam___closed__1;
x_6 = l_Lean_Meta_elimOptParam___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_elimOptParam___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_elimOptParam___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
lean_dec(x_1);
x_18 = lean_expr_instantiate1(x_2, x_10);
lean_dec(x_2);
lean_inc(x_10);
x_19 = lean_array_push(x_3, x_10);
x_20 = lean_array_push(x_4, x_10);
x_21 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(x_5, x_6, x_7, x_8, x_9, x_17, x_18, x_19, x_20, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected constructor type for '", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_6, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_apply_7(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = lean_whnf(x_7, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_array_fget(x_3, x_6);
lean_inc(x_4);
lean_inc(x_24);
x_25 = l_Lean_Expr_occurs(x_24, x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_26 = lean_box(x_2);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1___boxed), 15, 9);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_23);
lean_closure_set(x_27, 2, x_8);
lean_closure_set(x_27, 3, x_9);
lean_closure_set(x_27, 4, x_1);
lean_closure_set(x_27, 5, x_26);
lean_closure_set(x_27, 6, x_3);
lean_closure_set(x_27, 7, x_4);
lean_closure_set(x_27, 8, x_5);
if (x_2 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_28 = 1;
x_29 = 0;
x_30 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_21, x_28, x_22, x_27, x_29, x_10, x_11, x_12, x_13, x_20);
return x_30;
}
else
{
uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = 0;
x_33 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_21, x_31, x_22, x_27, x_32, x_10, x_11, x_12, x_13, x_20);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
lean_dec(x_21);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_6, x_34);
lean_dec(x_6);
x_36 = lean_expr_instantiate1(x_23, x_24);
lean_dec(x_23);
x_37 = lean_array_push(x_8, x_24);
x_6 = x_35;
x_7 = x_36;
x_8 = x_37;
x_14 = x_20;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_MessageData_ofName(x_41);
x_43 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1(x_46, x_10, x_11, x_12, x_13, x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_47;
}
}
else
{
uint8_t x_48; 
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
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_22; 
x_12 = lean_array_uget(x_1, x_3);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_4);
x_13 = x_29;
x_14 = x_9;
goto block_21;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_23, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_array_fget(x_25, x_26);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_26, x_35);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_37 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Lean_Meta_isProp(x_38, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_expr_eqv(x_12, x_34);
if (x_44 == 0)
{
lean_object* x_45; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_mkEqHEq(x_12, x_34, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_push(x_24, x_46);
lean_ctor_set(x_4, 1, x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_4);
x_13 = x_49;
x_14 = x_47;
goto block_21;
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_4);
x_13 = x_54;
x_14 = x_43;
goto block_21;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_34);
lean_dec(x_12);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_4);
x_13 = x_56;
x_14 = x_55;
goto block_21;
}
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_40, 0);
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_40);
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
lean_dec(x_23);
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_37);
if (x_61 == 0)
{
return x_37;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_37, 0);
x_63 = lean_ctor_get(x_37, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_37);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_23);
x_65 = lean_array_fget(x_25, x_26);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_26, x_66);
lean_dec(x_26);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_25);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_69 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_72 = l_Lean_Meta_isProp(x_70, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_expr_eqv(x_12, x_65);
if (x_76 == 0)
{
lean_object* x_77; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = l_Lean_Meta_mkEqHEq(x_12, x_65, x_5, x_6, x_7, x_8, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_array_push(x_24, x_78);
lean_ctor_set(x_4, 1, x_80);
lean_ctor_set(x_4, 0, x_68);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_4);
x_13 = x_81;
x_14 = x_79;
goto block_21;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_68);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_65);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_68);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_4);
x_13 = x_86;
x_14 = x_75;
goto block_21;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_65);
lean_dec(x_12);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
lean_ctor_set(x_4, 0, x_68);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_4);
x_13 = x_88;
x_14 = x_87;
goto block_21;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_68);
lean_dec(x_65);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_68);
lean_dec(x_65);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_ctor_get(x_69, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_95 = x_69;
} else {
 lean_dec_ref(x_69);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_4, 0);
x_98 = lean_ctor_get(x_4, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_4);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 2);
lean_inc(x_101);
x_102 = lean_nat_dec_lt(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_12);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_98);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_13 = x_104;
x_14 = x_9;
goto block_21;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
x_106 = lean_array_fget(x_99, x_100);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_100, x_107);
lean_dec(x_100);
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_101);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_110 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_113 = l_Lean_Meta_isProp(x_111, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_expr_eqv(x_12, x_106);
if (x_117 == 0)
{
lean_object* x_118; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Meta_mkEqHEq(x_12, x_106, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_array_push(x_98, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_13 = x_123;
x_14 = x_120;
goto block_21;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_109);
lean_dec(x_98);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
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
lean_object* x_128; lean_object* x_129; 
lean_dec(x_106);
lean_dec(x_12);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_109);
lean_ctor_set(x_128, 1, x_98);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_13 = x_129;
x_14 = x_116;
goto block_21;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_106);
lean_dec(x_12);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
lean_dec(x_113);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_109);
lean_ctor_set(x_131, 1, x_98);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_13 = x_132;
x_14 = x_130;
goto block_21;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_98);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_133 = lean_ctor_get(x_113, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_113, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_135 = x_113;
} else {
 lean_dec_ref(x_113);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_98);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_137 = lean_ctor_get(x_110, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_110, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_139 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
block_21:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
x_9 = x_14;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvarId_x21(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkForallFVars(x_1, x_4, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_mkForallFVars(x_2, x_14, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkForallFVars(x_3, x_17, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
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
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
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
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
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
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Expr_const___override(x_13, x_2);
lean_inc(x_3);
x_15 = l_Lean_mkAppN(x_14, x_3);
lean_inc(x_4);
lean_inc(x_15);
x_16 = l_Lean_mkAppN(x_15, x_4);
lean_inc(x_6);
x_17 = l_Lean_mkAppN(x_15, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_mkEq(x_16, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_toSubarray___rarg(x_6, x_22, x_21);
x_24 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_get_size(x_4);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1(x_4, x_27, x_28, x_25, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_box(0);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_free_object(x_29);
if (x_5 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkArrow(x_19, x_36, x_10, x_11, x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(x_7, x_4, x_3, x_38, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Meta_mkEq(x_19, x_41, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(x_7, x_4, x_3, x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
if (x_5 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_mkArrow(x_19, x_56, x_10, x_11, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(x_7, x_4, x_3, x_58, x_8, x_9, x_10, x_11, x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_62 = l_Lean_Meta_mkEq(x_19, x_61, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(x_7, x_4, x_3, x_63, x_8, x_9, x_10, x_11, x_64);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
return x_18;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_18, 0);
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_18);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(x_4);
lean_inc(x_7);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___boxed), 12, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_7);
lean_closure_set(x_15, 4, x_14);
if (x_4 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2(x_17, x_18, x_3);
x_20 = lean_array_get_size(x_7);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
lean_inc(x_7);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2(x_21, x_18, x_7);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
x_25 = lean_box(x_4);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_7);
lean_closure_set(x_26, 3, x_8);
lean_closure_set(x_26, 4, x_15);
lean_closure_set(x_26, 5, x_23);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_24);
lean_closure_set(x_26, 8, x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_withInstImplicitAsImplict___spec__3___rarg___boxed), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_withInstImplicitAsImplict___spec__3___rarg(x_19, x_27, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
x_31 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(x_5, x_4, x_7, x_8, x_15, x_29, x_6, x_30, x_30, x_9, x_10, x_11, x_12, x_13);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_3);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3___boxed), 13, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_6);
x_14 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_6, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_9, x_10);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = l_Lean_Meta_elimOptParam___closed__1;
x_14 = l_Lean_Meta_elimOptParam___closed__2;
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_12, x_13, x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(x_2);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4___boxed), 11, 4);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_11);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_1);
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_16, x_19, x_21, x_3, x_4, x_5, x_6, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__4(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to prove injectivity theorem for constructor '", 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', use 'set_option genInjectivity false' to disable the generation", 66);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_MessageData_ofName(x_1);
x_3 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(x_1);
x_9 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = l_Lean_indentD(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_MVarId_assumptionCore(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_21;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Injective", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Meta.Injective.0.Lean.Meta.solveEqOfCtorEq", 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1;
x_2 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2;
x_3 = lean_unsigned_to_nat(86u);
x_4 = lean_unsigned_to_nat(30u);
x_5 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_injection(x_2, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4;
x_14 = l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1(x_13, x_4, x_5, x_6, x_7, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_splitAndCore(x_16, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_forM___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__2(x_1, x_18, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_Array_back___rarg(x_14, x_2);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(x_1, x_13, x_16, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = 1;
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_19, x_20, x_21, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lambda__1), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inj", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 2);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
lean_inc(x_20);
x_23 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(x_20, x_18, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_mkInjectiveTheoremNameFor(x_20);
x_27 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_24, x_2, x_3, x_4, x_5, x_29);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_26);
lean_ctor_set(x_16, 2, x_28);
lean_ctor_set(x_16, 0, x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_addDecl(x_36, x_4, x_5, x_32);
return x_37;
}
else
{
uint8_t x_38; 
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
lean_inc(x_42);
x_44 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(x_42, x_18, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_mkInjectiveTheoremNameFor(x_42);
x_48 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_45, x_2, x_3, x_4, x_5, x_50);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_49);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_addDecl(x_58, x_4, x_5, x_53);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_62 = x_44;
} else {
 lean_dec_ref(x_44);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_8);
if (x_64 == 0)
{
return x_8;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_8);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("injEq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = 0;
x_10 = 1;
x_11 = 1;
x_12 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("propIntro", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected number of subgoals when proving injective theorem for constructor '", 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
x_14 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4;
x_15 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_MVarId_apply(x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MessageData_ofName(x_1);
x_20 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_23, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_2);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_MessageData_ofName(x_1);
x_28 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_31, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_intro1Core(x_35, x_37, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Meta_intro1Core(x_36, x_37, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_47 = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(x_1, x_42, x_41, x_4, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_49 = l_Lean_MVarId_casesAnd(x_46, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_MVarId_substEqs(x_50, x_4, x_5, x_6, x_7, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = 1;
x_56 = 1;
x_57 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_37, x_55, x_56, x_4, x_5, x_6, x_7, x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l_Lean_MVarId_refl(x_59, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = 1;
x_63 = 1;
x_64 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_37, x_62, x_63, x_4, x_5, x_6, x_7, x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_11);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
x_68 = l_Lean_Exception_isRuntime(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_free_object(x_60);
lean_dec(x_66);
x_69 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(x_1);
x_70 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_69, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = lean_ctor_get_uint8(x_6, sizeof(void*)*11);
if (x_75 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_free_object(x_60);
lean_dec(x_66);
x_76 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(x_1);
x_77 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_76, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_60, 0);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_60);
x_84 = l_Lean_Exception_isRuntime(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
x_85 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(x_1);
x_86 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_85, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_6, sizeof(void*)*11);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_83);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_93 = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(x_1);
x_94 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_93, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_52);
if (x_99 == 0)
{
return x_52;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_52, 0);
x_101 = lean_ctor_get(x_52, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_52);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_49);
if (x_103 == 0)
{
return x_49;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_49, 0);
x_105 = lean_ctor_get(x_49, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_49);
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
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_47);
if (x_107 == 0)
{
return x_47;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_47, 0);
x_109 = lean_ctor_get(x_47, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_47);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_43);
if (x_111 == 0)
{
return x_43;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_43, 0);
x_113 = lean_ctor_get(x_43, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_43);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_38);
if (x_115 == 0)
{
return x_38;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_38, 0);
x_117 = lean_ctor_get(x_38, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_38);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_2);
x_119 = lean_ctor_get(x_16, 1);
lean_inc(x_119);
lean_dec(x_16);
x_120 = l_Lean_MessageData_ofName(x_1);
x_121 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_124, x_4, x_5, x_6, x_7, x_119);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_16);
if (x_126 == 0)
{
return x_16;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_16, 0);
x_128 = lean_ctor_get(x_16, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_16);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 2);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
lean_inc(x_20);
x_23 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(x_20, x_18, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_mkInjectiveEqTheoremNameFor(x_20);
x_27 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_24, x_2, x_3, x_4, x_5, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_26);
lean_ctor_set(x_16, 2, x_28);
lean_ctor_set(x_16, 0, x_26);
x_33 = lean_box(0);
lean_inc(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_addDecl(x_36, x_4, x_5, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1;
x_40 = 0;
x_41 = 0;
x_42 = lean_unsigned_to_nat(1000u);
x_43 = l_Lean_Meta_addSimpTheorem(x_39, x_26, x_7, x_40, x_41, x_42, x_2, x_3, x_4, x_5, x_38);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
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
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
return x_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_16, 0);
x_53 = lean_ctor_get(x_16, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
lean_inc(x_52);
x_54 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(x_52, x_18, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_mkInjectiveEqTheoremNameFor(x_52);
x_58 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_55, x_2, x_3, x_4, x_5, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_57);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_59);
x_65 = lean_box(0);
lean_inc(x_57);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_addDecl(x_68, x_4, x_5, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1;
x_72 = 0;
x_73 = 0;
x_74 = lean_unsigned_to_nat(1000u);
x_75 = l_Lean_Meta_addSimpTheorem(x_71, x_57, x_7, x_72, x_73, x_74, x_2, x_3, x_4, x_5, x_70);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_54, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_54, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_82 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
}
else
{
uint8_t x_84; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_8);
if (x_84 == 0)
{
return x_8;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_8, 0);
x_86 = lean_ctor_get(x_8, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_8);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("genInjectivity", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("generate injectivity theorems for inductive datatype constructors", 65);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = l_Lean_MessageData_ofExpr(x_14);
x_16 = l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_27);
x_29 = l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3(x_32, x_2, x_3, x_4, x_5, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a constructor", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_17);
x_19 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4(x_22, x_2, x_3, x_4, x_5, x_15);
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
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_4, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2;
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 3);
lean_dec(x_11);
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3;
lean_ctor_set(x_8, 3, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_24 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3;
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_9);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___boxed), 2, 0);
return x_4;
}
}
static double _init_l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_io_mono_nanos_now(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_io_mono_nanos_now(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; double x_19; double x_20; double x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_nat_sub(x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Float_ofScientific(x_16, x_17, x_18);
lean_dec(x_16);
x_20 = l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1;
x_21 = lean_float_div(x_19, x_20);
x_22 = lean_box_float(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; double x_29; double x_30; double x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_nat_sub(x_24, x_8);
lean_dec(x_8);
lean_dec(x_24);
x_27 = 0;
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Float_ofScientific(x_26, x_27, x_28);
lean_dec(x_26);
x_30 = l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1;
x_31 = lean_float_div(x_29, x_30);
x_32 = lean_box_float(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_12, 3);
x_16 = l_Lean_PersistentArray_toArray___rarg(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(x_18, x_19, x_16);
x_21 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PersistentArray_push___rarg(x_1, x_22);
lean_ctor_set(x_12, 3, x_23);
x_24 = lean_st_ref_set(x_9, x_12, x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
x_33 = lean_ctor_get(x_12, 2);
x_34 = lean_ctor_get(x_12, 3);
x_35 = lean_ctor_get(x_12, 4);
x_36 = lean_ctor_get(x_12, 5);
x_37 = lean_ctor_get(x_12, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_38 = l_Lean_PersistentArray_toArray___rarg(x_34);
x_39 = lean_array_get_size(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(x_40, x_41, x_38);
x_43 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_4);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_PersistentArray_push___rarg(x_1, x_44);
x_46 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_46, 2, x_33);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 4, x_35);
lean_ctor_set(x_46, 5, x_36);
lean_ctor_set(x_46, 6, x_37);
x_47 = lean_st_ref_set(x_9, x_46, x_13);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_3, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 5, x_13);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get(x_8, 5);
x_24 = lean_ctor_get(x_8, 6);
x_25 = lean_ctor_get(x_8, 7);
x_26 = lean_ctor_get(x_8, 8);
x_27 = lean_ctor_get(x_8, 9);
x_28 = lean_ctor_get(x_8, 10);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_30 = l_Lean_replaceRef(x_3, x_23);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_24);
lean_ctor_set(x_31, 7, x_25);
lean_ctor_set(x_31, 8, x_26);
lean_ctor_set(x_31, 9, x_27);
lean_ctor_set(x_31, 10, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*11, x_29);
x_32 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_6, x_7, x_31, x_9, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10(x_1, x_2, x_3, x_33, x_5, x_6, x_7, x_31, x_9, x_34);
lean_dec(x_31);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Lean_Exception_isRuntime(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = l_Lean_Exception_isRuntime(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_10);
x_13 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9(x_1, x_2, x_3, x_6, x_4, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(x_5, x_8, x_9, x_10, x_11, x_14);
lean_dec(x_10);
return x_15;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("s] ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1;
x_17 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_6, x_16);
lean_dec(x_6);
if (x_17 == 0)
{
if (x_7 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_10, x_18, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_float_to_string(x_8);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_29, x_30, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_float_to_string(x_8);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
x_40 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_41, x_42, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_43;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<exception thrown while producing trace node message>", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_13, 5);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_17 = lean_apply_6(x_8, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_18, x_11, x_12, x_13, x_14, x_19);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
x_24 = l_Lean_Exception_isRuntime(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
lean_dec(x_22);
x_25 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2;
x_26 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_25, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_13, sizeof(void*)*11);
if (x_27 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_17);
lean_dec(x_22);
x_28 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2;
x_29 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_28, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = l_Lean_Exception_isRuntime(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_33 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2;
x_34 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_33, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*11);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_37 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2;
x_38 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_37, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_38;
}
}
}
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_14 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__1), 6, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8(x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_68; uint8_t x_69; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_68 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1;
x_69 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_4, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
x_23 = x_70;
goto block_67;
}
else
{
double x_71; double x_72; uint8_t x_73; 
x_71 = l_Lean_trace_profiler_threshold_getSecs(x_4);
x_72 = lean_unbox_float(x_22);
x_73 = lean_float_decLt(x_71, x_72);
x_23 = x_73;
goto block_67;
}
block_67:
{
if (x_6 == 0)
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = lean_st_ref_take(x_12, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_PersistentArray_append___rarg(x_15, x_28);
lean_ctor_set(x_25, 3, x_29);
x_30 = lean_st_ref_set(x_12, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(x_21, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_PersistentArray_append___rarg(x_15, x_44);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_46);
lean_ctor_set(x_49, 6, x_47);
x_50 = lean_st_ref_set(x_12, x_49, x_26);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(x_21, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_21);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; double x_62; lean_object* x_63; 
x_61 = lean_box(0);
x_62 = lean_unbox_float(x_22);
lean_dec(x_22);
x_63 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4(x_15, x_2, x_3, x_21, x_4, x_23, x_62, x_5, lean_box(0), x_61, x_9, x_10, x_11, x_12, x_20);
return x_63;
}
}
else
{
lean_object* x_64; double x_65; lean_object* x_66; 
x_64 = lean_box(0);
x_65 = lean_unbox_float(x_22);
lean_dec(x_22);
x_66 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4(x_15, x_2, x_3, x_21, x_4, x_23, x_65, x_5, lean_box(0), x_64, x_9, x_10, x_11, x_12, x_20);
return x_66;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
return x_18;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_18, 0);
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_18);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_12);
lean_dec(x_12);
x_28 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5(x_3, x_1, x_4, x_10, x_2, x_27, lean_box(0), x_26, x_5, x_6, x_7, x_8, x_14);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = lean_unbox(x_12);
lean_dec(x_12);
x_32 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5(x_3, x_1, x_4, x_10, x_2, x_31, lean_box(0), x_30, x_5, x_6, x_7, x_8, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_MessageData_ofName(x_1);
x_9 = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_15 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(x_9, x_2, x_3, x_4, x_5, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_29 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(x_22, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(x_22, x_2, x_3, x_4, x_5, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_34 = x_29;
} else {
 lean_dec_ref(x_29);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("injective", 9);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6;
x_2 = l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1___boxed), 7, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__2), 6, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2;
x_14 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5(x_13, x_11, x_12, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_1 = x_10;
x_2 = x_17;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_genInjectivity;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkInjectiveTheorems___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkInjectiveTheorems___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkInjectiveTheorems___closed__4;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_isInductivePredicate(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3;
x_17 = l_Lean_Environment_contains(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Meta_mkInjectiveTheorems___closed__1;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_19);
lean_dec(x_11);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
uint8_t x_22; 
x_22 = lean_unbox(x_14);
lean_dec(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_12);
x_23 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*5 + 1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 4);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lambda__1), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_mkInjectiveTheorems___closed__5;
x_30 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
x_31 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(x_29, x_30, x_28, x_2, x_3, x_4, x_5, x_26);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
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
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
lean_ctor_set(x_12, 0, x_42);
return x_12;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3;
x_46 = l_Lean_Environment_contains(x_10, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Meta_mkInjectiveTheorems___closed__1;
x_50 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_49);
lean_dec(x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = lean_unbox(x_43);
lean_dec(x_43);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*5 + 1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 4);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lambda__1), 6, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = l_Lean_Meta_mkInjectiveTheorems___closed__5;
x_61 = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1;
x_62 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(x_60, x_61, x_59, x_2, x_3, x_4, x_5, x_57);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_69 = x_54;
} else {
 lean_dec_ref(x_54);
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
lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_44);
return x_72;
}
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_mkInjectiveTheorems___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_mkInjectiveTheorems___spec__10(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__9(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Meta_mkInjectiveTheorems___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__2(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; double x_18; lean_object* x_19; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox_float(x_8);
lean_dec(x_8);
x_19 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3(x_1, x_2, x_3, x_16, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; double x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox_float(x_7);
lean_dec(x_7);
x_19 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4(x_1, x_2, x_16, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Injective", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12;
x_2 = lean_unsigned_to_nat(2157u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Injective(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f___spec__1___closed__3);
l_Lean_Meta_elimOptParam___lambda__1___closed__1 = _init_l_Lean_Meta_elimOptParam___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_elimOptParam___lambda__1___closed__1);
l_Lean_Meta_elimOptParam___lambda__1___closed__2 = _init_l_Lean_Meta_elimOptParam___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_elimOptParam___lambda__1___closed__2);
l_Lean_Meta_elimOptParam___lambda__1___closed__3 = _init_l_Lean_Meta_elimOptParam___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_elimOptParam___lambda__1___closed__3);
l_Lean_Meta_elimOptParam___closed__1 = _init_l_Lean_Meta_elimOptParam___closed__1();
lean_mark_persistent(l_Lean_Meta_elimOptParam___closed__1);
l_Lean_Meta_elimOptParam___closed__2 = _init_l_Lean_Meta_elimOptParam___closed__2();
lean_mark_persistent(l_Lean_Meta_elimOptParam___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__4);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lambda__2___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__4);
l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___rarg___closed__2);
l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___spec__1___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4);
l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1 = _init_l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1);
l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2 = _init_l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__2);
l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1 = _init_l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1();
lean_mark_persistent(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1);
l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2 = _init_l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2();
lean_mark_persistent(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__1);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__2);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__3);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__4);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__5);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__6);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lambda__2___closed__7);
l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1 = _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818____closed__7);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_1818_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_genInjectivity = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_genInjectivity);
lean_dec_ref(res);
}l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__1);
l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_mkInjectiveTheorems___spec__2___closed__2);
l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__1);
l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_mkInjectiveTheorems___spec__1___closed__2);
l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_mkInjectiveTheorems___spec__6___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__2);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_mkInjectiveTheorems___spec__7___rarg___closed__3);
l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1 = _init_l_Lean_withSeconds___at_Lean_Meta_mkInjectiveTheorems___spec__8___closed__1();
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__3);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__4);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__3___closed__5);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_mkInjectiveTheorems___spec__5___lambda__5___closed__1);
l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1 = _init_l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__1);
l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2 = _init_l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Meta_mkInjectiveTheorems___spec__12___closed__2);
l_Lean_Meta_mkInjectiveTheorems___closed__1 = _init_l_Lean_Meta_mkInjectiveTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheorems___closed__1);
l_Lean_Meta_mkInjectiveTheorems___closed__2 = _init_l_Lean_Meta_mkInjectiveTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheorems___closed__2);
l_Lean_Meta_mkInjectiveTheorems___closed__3 = _init_l_Lean_Meta_mkInjectiveTheorems___closed__3();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheorems___closed__3);
l_Lean_Meta_mkInjectiveTheorems___closed__4 = _init_l_Lean_Meta_mkInjectiveTheorems___closed__4();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheorems___closed__4);
l_Lean_Meta_mkInjectiveTheorems___closed__5 = _init_l_Lean_Meta_mkInjectiveTheorems___closed__5();
lean_mark_persistent(l_Lean_Meta_mkInjectiveTheorems___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157____closed__13);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Injective___hyg_2157_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
