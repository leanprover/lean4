// Lean compiler output
// Module: Lean.Util.Trace
// Imports: Init Lean.Message Lean.MonadEnv
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
lean_object* lean_string_push(lean_object*, uint32_t);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_1842____closed__8;
lean_object* l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__7;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_MessageData_isNest(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_withNestedTraces___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withNestedTraces___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6(lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___kind_tactic____x40_Init_Tactics___hyg_461____closed__10;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(size_t, size_t, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14;
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5;
lean_object* l_Lean_traceCtx___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean___kind_term____x40_Lean_Exception___hyg_643____closed__7;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5;
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l_Lean_getTraces(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7;
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__3;
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_findSomeM_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
lean_object* l_Lean_withNestedTraces___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_502____closed__7;
lean_object* l_Lean_traceM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean___kind_term____x40_Lean_Message___hyg_1842____closed__4;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8;
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251_;
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889_;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4;
lean_object* l_Lean_setTraceState(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2;
lean_object* l_Lean_withNestedTraces(lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode(lean_object*);
lean_object* l_Lean_traceM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_enableTracing___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces(lean_object*);
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2(lean_object*);
extern lean_object* l_Lean___kind_term____x40_Lean_Exception___hyg_684____closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
lean_object* l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1;
lean_object* l_Lean_Lean_Util_Trace___instance__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4;
lean_object* l_Lean_enableTracing___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass___closed__2;
lean_object* l_Lean_traceCtx___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_isNil(lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceM(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_MessageData_nil___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2___closed__1;
lean_object* l_Lean_isTracingEnabledFor(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6;
lean_object* l_Lean_withNestedTraces___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState___rarg(lean_object*);
lean_object* l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__1(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withNestedTraces___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
lean_object* l_Lean_enableTracing(lean_object*);
lean_object* l_Lean_withNestedTraces___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5(lean_object*);
lean_object* l_Lean_addTrace___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg(lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__8;
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3;
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__4;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__9;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState(lean_object*);
lean_object* l_Lean_MonadTracer_trace(lean_object*);
lean_object* l_Lean_setTraceState___rarg(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___closed__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux_match__1(lean_object*);
lean_object* l_Lean_TraceState_traces___default;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1;
lean_object* l_IO_println___at_Lean_printTraces___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_TraceState_Lean_Util_Trace___instance__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l_Lean_enableTracing___rarg___lambda__2(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19;
lean_object* l_Lean_withNestedTraces___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces(lean_object*);
extern lean_object* l_Lean_Name_hasMacroScopes___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12;
lean_object* l_Lean_checkTraceOption___boxed(lean_object*, lean_object*);
lean_object* l_Lean_checkTraceOption___closed__1;
lean_object* l_IO_print___at_Lean_Init_System_IO___instance__9___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_traceM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace(lean_object*);
lean_object* l_Lean_resetTraceState___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState___rarg___lambda__1(lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__1(uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5;
lean_object* l_Lean_trace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TraceState_enabled___default;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3;
lean_object* l_Lean_getTraces___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3(lean_object*);
lean_object* l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Util_Trace___instance__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__1(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Lean_Util_Trace___instance__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2(lean_object*, size_t, size_t);
lean_object* l_Lean_Lean_Util_Trace___instance__3(lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
lean_object* l_Lean_getTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_withNestedTraces___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2;
lean_object* l_Lean_traceCtx___rarg___lambda__3(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_checkTraceOption___closed__2;
extern lean_object* l_tryFinally___rarg___closed__1;
lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6;
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Exception___hyg_731____closed__9;
lean_object* l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_TraceState_toFormat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Util_Trace___instance__1___closed__1;
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Lean_Util_Trace___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_nil___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lean_Util_Trace___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lean_Util_Trace___instance__1___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_TraceState_enabled___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_TraceState_traces___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Std_PersistentArray_empty___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_TraceState_Lean_Util_Trace___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
return x_1;
}
}
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_usize_to_nat(x_2);
x_18 = l_Lean_Lean_Util_Trace___instance__1;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_usize_of_nat(x_2);
x_7 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_8 = l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lean_Lean_Util_Trace___instance__1;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(x_1, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_MessageData_format(x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_nat_dec_lt(x_7, x_12);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_16);
x_4 = x_10;
x_5 = x_19;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_2);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_4 = x_10;
x_5 = x_22;
x_6 = x_17;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_TraceState_toFormat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3(x_1, x_2, x_4, x_4, x_5, x_3);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_getAux___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldM_loop___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Lean_Util_Trace___instance__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Lean_Util_Trace___instance__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Util_Trace___instance__3___rarg___lambda__1), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Lean_Util_Trace___instance__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lean_Util_Trace___instance__3___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_println___at_Lean_printTraces___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = l_Lean_Format_pretty(x_1, x_3);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_print___at_Lean_Init_System_IO___instance__9___spec__2(x_6, x_2);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = x_1 + x_8;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg(x_2, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_5 == x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3___rarg(x_1, x_2, x_3, x_10);
x_12 = lean_box_usize(x_5);
x_13 = lean_box_usize(x_6);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_7);
return x_18;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_println___at_Lean_printTraces___spec__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = x_1 + x_8;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg(x_2, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_5 == x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_MessageData_format), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_2);
lean_inc(x_3);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_14);
x_16 = lean_box_usize(x_5);
x_17 = lean_box_usize(x_6);
x_18 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_7);
return x_22;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_6, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg(x_1, x_2, x_3, x_5, x_18, x_19, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_23, x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_37 = lean_box(0);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg(x_1, x_2, x_3, x_22, x_35, x_36, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = x_1 + x_8;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg(x_2, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_5 == x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_MessageData_format), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_2);
lean_inc(x_3);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_14);
x_16 = lean_box_usize(x_5);
x_17 = lean_box_usize(x_6);
x_18 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_7);
return x_22;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_forMAux___at_Lean_printTraces___spec__3___rarg(x_1, x_2, x_3, x_7);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
x_16 = lean_apply_3(x_6, lean_box(0), x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_10, x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_apply_3(x_6, lean_box(0), x_8, x_20);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_22 = 0;
x_23 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg(x_1, x_2, x_3, x_9, x_22, x_23, x_24);
x_26 = lean_apply_3(x_6, lean_box(0), x_8, x_25);
return x_26;
}
}
}
}
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_printTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_printTraces___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_printTraces___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_printTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_printTraces___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__4___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___lambda__2(x_8, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__5___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_printTraces___spec__6___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Lean_resetTraceState___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_resetTraceState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_resetTraceState___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_resetTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_resetTraceState___rarg___closed__1;
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_resetTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resetTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_resetTraceState___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_resetTraceState___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_4(x_2, x_1, x_4, x_5, x_7);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = 0;
x_5 = l_Lean_KVMap_getBool(x_1, x_2, x_4);
x_6 = l_Lean_KVMap_contains(x_1, x_2);
if (x_6 == 0)
{
if (x_5 == 0)
{
x_2 = x_3;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
return x_5;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_checkTraceOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace");
return x_1;
}
}
static lean_object* _init_l_Lean_checkTraceOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_checkTraceOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_checkTraceOption(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_isEmpty___rarg(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_checkTraceOption___closed__2;
x_5 = l_Lean_Name_append(x_4, x_2);
x_6 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionAux(x_1, x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_checkTraceOption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_checkTraceOption(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_checkTraceOption(x_3, x_2);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg(x_1, x_2, x_3);
return x_11;
}
}
}
lean_object* l_Lean_isTracingEnabledFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_isTracingEnabledFor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_1);
return x_5;
}
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_apply_1(x_7, x_9);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_enableTracing___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_box(x_3);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___lambda__3___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_enableTracing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_enableTracing___rarg___lambda__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_enableTracing___rarg___lambda__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_enableTracing___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_enableTracing___rarg___lambda__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_enableTracing___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_enableTracing___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_getTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_getTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_getTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getTraces___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_modifyTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_6);
return x_9;
}
}
}
lean_object* l_Lean_modifyTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_modifyTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_modifyTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_modifyTraces___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_setTraceState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_setTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setTraceState___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Std_PersistentArray_isEmpty___rarg(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = l_Std_PersistentArray_toArray___rarg(x_6);
lean_dec(x_6);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = x_8;
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_10, x_11, x_12);
x_14 = x_13;
x_15 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Std_PersistentArray_push___rarg(x_3, x_17);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Std_PersistentArray_isEmpty___rarg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = l_Std_PersistentArray_toArray___rarg(x_20);
lean_dec(x_20);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = x_22;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_24, x_25, x_26);
x_28 = x_27;
x_29 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_PersistentArray_push___rarg(x_3, x_31);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_19);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_19);
return x_34;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addNode___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = l_Std_PersistentArray_empty___closed__1;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1;
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_addTrace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_PersistentArray_push___rarg(x_6, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_PersistentArray_push___rarg(x_11, x_13);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_10);
return x_15;
}
}
}
lean_object* l_Lean_addTrace___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_addTrace___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___lambda__2), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_addTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___lambda__3), 6, 5);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_addTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_trace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = l_Lean_addTrace___rarg(x_1, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
}
lean_object* l_Lean_trace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_trace___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_6);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_trace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_trace___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_trace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_trace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_traceM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_13);
return x_14;
}
}
}
lean_object* l_Lean_traceM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_traceM___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_6);
lean_closure_set(x_12, 5, x_8);
lean_closure_set(x_12, 6, x_7);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_traceM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_traceM___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_traceM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_traceM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_3);
return x_1;
}
else
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 0;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_traceCtx___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_traceCtx___rarg___lambda__2___closed__1;
x_8 = lean_apply_1(x_6, x_7);
x_9 = lean_box(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_enableTracing___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_apply_1(x_7, x_9);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_box(x_7);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__4___boxed), 5, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_11);
x_13 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_13);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_tryFinally___rarg___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg(x_2, x_7, x_3, x_4);
x_11 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_11);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_tryFinally___rarg___closed__1;
x_15 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg(x_1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__6), 7, 6);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_inc(x_3);
lean_inc(x_4);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_10);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__7), 7, 6);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_3);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_traceCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_8);
lean_inc(x_9);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__8___boxed), 9, 8);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_9);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_3);
lean_closure_set(x_12, 7, x_6);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_traceCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceCtx___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_traceCtx___rarg___lambda__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_traceCtx___rarg___lambda__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_traceCtx___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Lean_traceCtx___rarg___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_MonadTracer_trace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_trace___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_6);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_MonadTracer_trace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MonadTracer_trace___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_registerTraceClass___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("enable/disable tracing for the given module and submodules");
return x_1;
}
}
static lean_object* _init_l_Lean_registerTraceClass___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_2 = l_Lean_checkTraceOption___closed__1;
x_3 = l_Lean_registerTraceClass___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_registerTraceClass(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_checkTraceOption___closed__2;
x_4 = l_Lean_Name_append(x_3, x_1);
x_5 = l_Lean_registerTraceClass___closed__2;
x_6 = lean_register_option(x_4, x_5, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Util");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Message___hyg_1842____closed__4;
x_2 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Trace");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2;
x_2 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4;
x_2 = l_Lean_Name_hasMacroScopes___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5;
x_2 = lean_unsigned_to_nat(889u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace!");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8;
x_2 = l_Lean___kind_term____x40_Lean_Exception___hyg_684____closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9;
x_2 = l___kind_tactic____x40_Init_Tactics___hyg_461____closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_checkTraceOption___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_checkTraceOption___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_checkTraceOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fun");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("basicFun");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_myMacro____x40_Init_Tactics___hyg_502____closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_checkTraceOption___closed__2;
lean_inc(x_18);
lean_inc(x_19);
x_21 = l_Lean_addMacroScope(x_19, x_20, x_18);
x_22 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_23 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2;
x_24 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = lean_array_push(x_26, x_15);
x_29 = lean_array_push(x_26, x_17);
x_30 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__8;
x_31 = l_Lean_addMacroScope(x_19, x_30, x_18);
x_32 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__7;
x_33 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19;
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_33);
x_35 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__4;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_26, x_38);
x_40 = l_Lean_nullKind___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_array_push(x_29, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_45 = lean_array_push(x_44, x_43);
x_46 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_47 = lean_array_push(x_45, x_46);
x_48 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__3;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_28, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_27, x_59);
x_61 = l_Lean_mkAppStx___closed__8;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5;
x_2 = lean_unsigned_to_nat(1251u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace[");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3;
x_2 = lean_box(19);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]!");
return x_1;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4;
x_2 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7;
x_2 = l_Lean___kind_term____x40_Lean_Exception___hyg_643____closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1;
x_2 = lean_unsigned_to_nat(1023u);
x_3 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.trace");
return x_1;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Lean_interpolatedStrKind;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3;
lean_inc(x_21);
lean_inc(x_22);
x_24 = l_Lean_addMacroScope(x_22, x_23, x_21);
x_25 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_26 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3;
x_27 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5;
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Array_empty___closed__1;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_32 = l___private_Init_LeanInit_0__Lean_quoteName(x_31);
x_33 = lean_array_push(x_29, x_32);
x_34 = lean_array_push(x_29, x_17);
x_35 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__8;
x_36 = l_Lean_addMacroScope(x_22, x_35, x_21);
x_37 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__7;
x_38 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19;
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__4;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_29, x_43);
x_45 = l_Lean_nullKind___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_34, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_myMacro____x40_Init_Tactics___hyg_720____closed__6;
x_50 = lean_array_push(x_49, x_48);
x_51 = l_myMacro____x40_Init_Tactics___hyg_720____closed__10;
x_52 = lean_array_push(x_50, x_51);
x_53 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__3;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
x_56 = lean_array_push(x_55, x_54);
x_57 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_60 = lean_array_push(x_59, x_58);
x_61 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_array_push(x_33, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_push(x_30, x_64);
x_66 = l_Lean_mkAppStx___closed__8;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3;
x_72 = l_Lean_addMacroScope(x_70, x_71, x_69);
x_73 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_74 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3;
x_75 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5;
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_75);
x_77 = l_Array_empty___closed__1;
x_78 = lean_array_push(x_77, x_76);
x_79 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_80 = l___private_Init_LeanInit_0__Lean_quoteName(x_79);
x_81 = lean_array_push(x_77, x_80);
x_82 = l_Lean_myMacro____x40_Lean_Exception___hyg_731____closed__9;
x_83 = lean_array_push(x_82, x_17);
x_84 = l_Lean___kind_term____x40_Lean_Message___hyg_1842____closed__8;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17;
x_87 = lean_array_push(x_86, x_85);
x_88 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9;
x_91 = lean_array_push(x_90, x_89);
x_92 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_81, x_93);
x_95 = l_Lean_nullKind___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_78, x_96);
x_98 = l_Lean_mkAppStx___closed__8;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_3);
return x_100;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3(x_6, x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_MessageData_isNil(x_4);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_2 = x_9;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_2 = x_9;
x_4 = x_18;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3;
x_7 = lean_usize_to_nat(x_6);
x_8 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3;
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_MessageData_nil;
x_12 = l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(x_5, x_11, x_7);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_PersistentArray_push___rarg(x_2, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_5);
x_17 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(x_5, x_7);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_MessageData_isNest(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_MessageData_nil;
x_21 = l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(x_5, x_20, x_7);
lean_dec(x_5);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_PersistentArray_push___rarg(x_2, x_24);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = l_Std_PersistentArray_append___rarg(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_MessageData_nil;
x_35 = l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(x_28, x_34, x_30);
lean_dec(x_28);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Std_PersistentArray_push___rarg(x_2, x_38);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_27);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_28);
x_41 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_0__Lean_TraceState_toFormat___spec__1(x_28, x_30);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_MessageData_isNest(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = l_Lean_MessageData_nil;
x_45 = l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(x_28, x_44, x_30);
lean_dec(x_28);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_PersistentArray_push___rarg(x_2, x_48);
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_27);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_51 = l_Std_PersistentArray_append___rarg(x_2, x_28);
lean_dec(x_28);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_27);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_27);
return x_53;
}
}
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_1(x_3, x_9);
x_11 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_11);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_tryFinally___rarg___closed__1;
x_15 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg___lambda__2), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1;
lean_inc(x_8);
x_10 = lean_apply_1(x_8, x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg___lambda__3___boxed), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_2);
lean_inc(x_3);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_10);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg___lambda__4), 7, 6);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_1);
lean_closure_set(x_12, 5, x_3);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_withNestedTraces___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg___lambda__5___boxed), 8, 7);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_2);
lean_closure_set(x_8, 5, x_3);
lean_closure_set(x_8, 6, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_withNestedTraces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_withNestedTraces___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_withNestedTraces___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_withNestedTraces___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at_Lean_withNestedTraces___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withNestedTraces___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_withNestedTraces___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withNestedTraces___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_MonadEnv(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Trace(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lean_Util_Trace___instance__1___closed__1 = _init_l_Lean_Lean_Util_Trace___instance__1___closed__1();
lean_mark_persistent(l_Lean_Lean_Util_Trace___instance__1___closed__1);
l_Lean_Lean_Util_Trace___instance__1 = _init_l_Lean_Lean_Util_Trace___instance__1();
lean_mark_persistent(l_Lean_Lean_Util_Trace___instance__1);
l_Lean_TraceState_enabled___default = _init_l_Lean_TraceState_enabled___default();
l_Lean_TraceState_traces___default = _init_l_Lean_TraceState_traces___default();
lean_mark_persistent(l_Lean_TraceState_traces___default);
l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1 = _init_l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1();
lean_mark_persistent(l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1);
l_Lean_TraceState_Lean_Util_Trace___instance__2 = _init_l_Lean_TraceState_Lean_Util_Trace___instance__2();
lean_mark_persistent(l_Lean_TraceState_Lean_Util_Trace___instance__2);
l_Lean_resetTraceState___rarg___closed__1 = _init_l_Lean_resetTraceState___rarg___closed__1();
lean_mark_persistent(l_Lean_resetTraceState___rarg___closed__1);
l_Lean_checkTraceOption___closed__1 = _init_l_Lean_checkTraceOption___closed__1();
lean_mark_persistent(l_Lean_checkTraceOption___closed__1);
l_Lean_checkTraceOption___closed__2 = _init_l_Lean_checkTraceOption___closed__2();
lean_mark_persistent(l_Lean_checkTraceOption___closed__2);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___rarg___lambda__2___closed__1);
l_Lean_traceCtx___rarg___lambda__2___closed__1 = _init_l_Lean_traceCtx___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_traceCtx___rarg___lambda__2___closed__1);
l_Lean_registerTraceClass___closed__1 = _init_l_Lean_registerTraceClass___closed__1();
lean_mark_persistent(l_Lean_registerTraceClass___closed__1);
l_Lean_registerTraceClass___closed__2 = _init_l_Lean_registerTraceClass___closed__2();
lean_mark_persistent(l_Lean_registerTraceClass___closed__2);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__1);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__2);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__3);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__4);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__5);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__6);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__7);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__8);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__9);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__10);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889____closed__11);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889_ = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889_();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_889_);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__1);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__2);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__3);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__4);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__5);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__6);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__7);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__8);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__9);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__10);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__11);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__12);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__13);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__14);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__15);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__16);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__17);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__18);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_955____closed__19);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__1);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__2);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__3);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__4);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__5);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__6);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__7);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__8);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9 = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251____closed__9);
l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251_ = _init_l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251_();
lean_mark_persistent(l_Lean___kind_term____x40_Lean_Util_Trace___hyg_1251_);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__1);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__2);
l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3 = _init_l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3();
lean_mark_persistent(l_Lean_myMacro____x40_Lean_Util_Trace___hyg_1321____closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
