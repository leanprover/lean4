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
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_printTraces___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass___closed__1;
lean_object* l___private_Lean_Util_Trace_4__addNode___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState___rarg___closed__1;
lean_object* l_Lean_registerTraceClass___closed__3;
lean_object* l_Lean_enableTracing___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TraceState_Inhabited;
lean_object* l_Lean_traceCtx___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2(lean_object*, size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__1(lean_object*);
lean_object* l_Lean_getTraces(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l___private_Lean_Util_Trace_2__checkTraceOptionAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_traceM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace(lean_object*);
lean_object* l_Lean_monadTraceTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setTraceState(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_2__checkTraceOptionAux(lean_object*, lean_object*);
lean_object* l_Lean_traceM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_2__checkTraceOptionAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadTraceTrans(lean_object*, lean_object*);
lean_object* l_Lean_traceM(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2___closed__1;
lean_object* l_Lean_isTracingEnabledFor(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState___rarg(lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_traceCtx___rarg___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing(lean_object*);
lean_object* l_Lean_addTrace___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_finally___rarg___closed__1;
lean_object* l_Lean_addTrace___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_Lean_modifyTraces___rarg(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resetTraceState(lean_object*);
lean_object* l_Lean_MonadTracer_trace(lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_setTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_monadTraceTrans___rarg(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx(lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_printTraces___spec__1(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_traceElem_inhabited;
lean_object* l_Lean_traceCtx___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__2(lean_object*, uint8_t, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Util_Trace_4__addNode___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkTraceOption___boxed(lean_object*, lean_object*);
lean_object* l_Lean_setTraceState___boxed(lean_object*, lean_object*);
lean_object* l_Lean_checkTraceOption___closed__1;
lean_object* l_Lean_traceM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace(lean_object*);
lean_object* l_Lean_resetTraceState___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__checkTraceOptionAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___boxed(lean_object*, lean_object*);
lean_object* l_Lean_traceElem_inhabited___closed__1;
lean_object* l_Lean_resetTraceState___rarg___lambda__1(lean_object*);
lean_object* l_Lean_enableTracing___rarg___lambda__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Util_Trace_1__toFormat(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_trace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at___private_Init_System_IO_1__printlnAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_printTraces___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getTraces___rarg(lean_object*, lean_object*);
lean_object* l_Lean_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__1(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM(lean_object*);
lean_object* l_Lean_traceCtx___rarg___lambda__3(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6(lean_object*);
lean_object* l_Lean_checkTraceOption___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modifyTraces___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_traceElem_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_traceElem_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_traceElem_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TraceState_Inhabited___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Std_PersistentArray_empty___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_TraceState_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TraceState_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
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
x_7 = l_Std_PersistentArray_getAux___main___rarg___closed__1;
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
x_18 = l_Lean_traceElem_inhabited;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2(x_5, x_6, x_7);
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
x_11 = l_Lean_traceElem_inhabited;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1(x_1, x_12);
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
uint8_t x_19; lean_object* x_20; 
x_19 = 0;
x_20 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_4 = x_10;
x_5 = x_20;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
lean_inc(x_2);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_22);
x_4 = x_10;
x_5 = x_24;
x_6 = x_17;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
lean_object* l___private_Lean_Util_Trace_1__toFormat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3(x_1, x_2, x_4, x_4, x_5, x_3);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_getAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_get_x21___at___private_Lean_Util_Trace_1__toFormat___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at___private_Lean_Util_Trace_1__toFormat___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_monadTraceTrans___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_monadTraceTrans___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_monadTraceTrans___rarg___lambda__1), 3, 2);
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
lean_object* l_Lean_monadTraceTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_monadTraceTrans___rarg), 2, 0);
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
x_7 = l_IO_print___at___private_Init_System_IO_1__printlnAux___spec__2(x_6, x_2);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3___rarg(x_1, x_2, x_3, x_12);
x_15 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_println___at_Lean_printTraces___spec__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_MessageData_format), 2, 1);
lean_closure_set(x_15, 0, x_14);
lean_inc(x_2);
x_16 = lean_apply_2(x_2, lean_box(0), x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__1), 2, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_3);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg(x_1, x_2, x_3, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_MessageData_format), 2, 1);
lean_closure_set(x_15, 0, x_14);
lean_inc(x_2);
x_16 = lean_apply_2(x_2, lean_box(0), x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__1), 2, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_3);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_forM___at_Lean_printTraces___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_forMAux___main___at_Lean_printTraces___spec__3___rarg(x_1, x_2, x_3, x_7);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg(x_1, x_2, x_3, x_9, x_10);
x_12 = lean_apply_3(x_6, lean_box(0), x_8, x_11);
return x_12;
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
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at_Lean_printTraces___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at_Lean_printTraces___spec__5___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at_Lean_printTraces___spec__6___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_resetTraceState___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TraceState_Inhabited___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_resetTraceState___rarg___closed__1() {
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
uint8_t l___private_Lean_Util_Trace_2__checkTraceOptionAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = 0;
x_5 = l_Lean_KVMap_getBool(x_1, x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_KVMap_contains(x_1, x_2);
if (x_6 == 0)
{
x_2 = x_3;
goto _start;
}
else
{
return x_5;
}
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
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l___private_Lean_Util_Trace_2__checkTraceOptionAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_Trace_2__checkTraceOptionAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Lean_Util_Trace_2__checkTraceOptionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Util_Trace_2__checkTraceOptionAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_2__checkTraceOptionAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_Trace_2__checkTraceOptionAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_checkTraceOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace");
return x_1;
}
}
lean_object* _init_l_Lean_checkTraceOption___closed__2() {
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
x_5 = l_Lean_Name_append___main(x_4, x_2);
x_6 = l___private_Lean_Util_Trace_2__checkTraceOptionAux___main(x_1, x_5);
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
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_3__checkTraceOptionM___rarg(x_1, x_2, x_3, x_4);
return x_12;
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
x_7 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
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
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_isTracingEnabledFor___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
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
lean_object* l_Lean_modifyTraces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_modifyTraces___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_modifyTraces___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_modifyTraces(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* l_Lean_setTraceState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_setTraceState___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_setTraceState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_setTraceState(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Util_Trace_4__addNode___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Std_PersistentArray_toArray___rarg(x_6);
lean_dec(x_6);
x_8 = x_7;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_umapMAux___main___at___private_Lean_Util_Trace_4__addNode___spec__1(x_9, x_8);
x_11 = x_10;
x_12 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_PersistentArray_push___rarg(x_3, x_14);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Std_PersistentArray_toArray___rarg(x_17);
lean_dec(x_17);
x_19 = x_18;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_umapMAux___main___at___private_Lean_Util_Trace_4__addNode___spec__1(x_20, x_19);
x_22 = x_21;
x_23 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_PersistentArray_push___rarg(x_3, x_25);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_16);
return x_27;
}
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_4__addNode___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_4__addNode___rarg), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_4__addNode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_4__addNode(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Std_PersistentArray_empty___closed__3;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = l_Std_PersistentArray_empty___closed__3;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
}
}
lean_object* _init_l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1;
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_5__getResetTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_5__getResetTraces___rarg), 2, 0);
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
lean_object* l_Lean_addTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___lambda__3), 6, 5);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_6);
lean_closure_set(x_10, 4, x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_addTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_addTrace___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_trace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
x_15 = l_Lean_addTrace___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_14);
return x_15;
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
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_trace___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
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
lean_object* l_Lean_trace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_trace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Lean_traceM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_addTrace___rarg___boxed), 7, 6);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_14);
return x_15;
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
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_traceM___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_7);
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
lean_object* l_Lean_traceM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Lean_traceM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
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
lean_object* _init_l_Lean_traceCtx___rarg___lambda__2___closed__1() {
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
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_14);
x_16 = l_finally___rarg___closed__1;
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_15);
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
x_10 = l___private_Lean_Util_Trace_4__addNode___rarg(x_2, x_7, x_3, x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_12);
x_14 = l_finally___rarg___closed__1;
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
lean_object* l_Lean_traceCtx___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Util_Trace_5__getResetTraces___rarg(x_1, x_2);
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
lean_object* l_Lean_traceCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_7);
lean_inc(x_9);
lean_inc(x_10);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___lambda__8___boxed), 9, 8);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_8);
lean_closure_set(x_13, 6, x_3);
lean_closure_set(x_13, 7, x_7);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_traceCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_traceCtx___rarg___boxed), 8, 0);
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
lean_object* l_Lean_traceCtx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_traceCtx___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
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
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_6);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_trace___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
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
lean_object* _init_l_Lean_registerTraceClass___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_registerTraceClass___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("enable/disable tracing for the given module and submodules");
return x_1;
}
}
lean_object* _init_l_Lean_registerTraceClass___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerTraceClass___closed__1;
x_2 = l_Lean_checkTraceOption___closed__1;
x_3 = l_Lean_registerTraceClass___closed__2;
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
x_4 = l_Lean_Name_append___main(x_3, x_1);
x_5 = l_Lean_registerTraceClass___closed__3;
x_6 = lean_register_option(x_4, x_5, x_2);
return x_6;
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
l_Lean_traceElem_inhabited___closed__1 = _init_l_Lean_traceElem_inhabited___closed__1();
lean_mark_persistent(l_Lean_traceElem_inhabited___closed__1);
l_Lean_traceElem_inhabited = _init_l_Lean_traceElem_inhabited();
lean_mark_persistent(l_Lean_traceElem_inhabited);
l_Lean_TraceState_Inhabited___closed__1 = _init_l_Lean_TraceState_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TraceState_Inhabited___closed__1);
l_Lean_TraceState_Inhabited = _init_l_Lean_TraceState_Inhabited();
lean_mark_persistent(l_Lean_TraceState_Inhabited);
l_Lean_resetTraceState___rarg___closed__1 = _init_l_Lean_resetTraceState___rarg___closed__1();
lean_mark_persistent(l_Lean_resetTraceState___rarg___closed__1);
l_Lean_checkTraceOption___closed__1 = _init_l_Lean_checkTraceOption___closed__1();
lean_mark_persistent(l_Lean_checkTraceOption___closed__1);
l_Lean_checkTraceOption___closed__2 = _init_l_Lean_checkTraceOption___closed__2();
lean_mark_persistent(l_Lean_checkTraceOption___closed__2);
l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1 = _init_l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_5__getResetTraces___rarg___lambda__2___closed__1);
l_Lean_traceCtx___rarg___lambda__2___closed__1 = _init_l_Lean_traceCtx___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_traceCtx___rarg___lambda__2___closed__1);
l_Lean_registerTraceClass___closed__1 = _init_l_Lean_registerTraceClass___closed__1();
lean_mark_persistent(l_Lean_registerTraceClass___closed__1);
l_Lean_registerTraceClass___closed__2 = _init_l_Lean_registerTraceClass___closed__2();
lean_mark_persistent(l_Lean_registerTraceClass___closed__2);
l_Lean_registerTraceClass___closed__3 = _init_l_Lean_registerTraceClass___closed__3();
lean_mark_persistent(l_Lean_registerTraceClass___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
