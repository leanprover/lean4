// Lean compiler output
// Module: Init.Lean.Trace
// Imports: Init.Lean.Message
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
lean_object* l___private_Init_Lean_Trace_3__addTrace___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode(lean_object*, lean_object*);
lean_object* l_Lean_monadTracerAdapter___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinArraySep___at_Lean_TraceState_Lean_HasFormat___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinArraySep___at_Lean_TraceState_Lean_HasFormat___spec__1___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Trace_4__checkTraceOptionAux(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg(lean_object*, uint8_t);
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___boxed(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadTracerAdapterExcept___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TraceState_HasToString___closed__1;
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MonadTracerAdapter_traceCtx(lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing(lean_object*, lean_object*);
lean_object* l_Lean_TraceState_HasToString;
lean_object* l_Lean_TraceState_Inhabited;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_4__checkTraceOptionAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_trace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1;
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption(lean_object*);
lean_object* l_Lean_TraceState_HasToString___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___boxed(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Trace_3__addTrace(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_monadTracerAdapterExcept(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_monadTracerAdapter(lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___rarg(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_trace___boxed(lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapter(lean_object*);
uint8_t l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_MonadTracerAdapter_trace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_monadTracerAdapter___boxed(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TraceState_Lean_HasFormat___boxed(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1___boxed(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadTracerAdapterExcept___boxed(lean_object*, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapter___boxed(lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor(lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces(lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1(uint8_t, lean_object*);
lean_object* l_Lean_simpleMonadTracerAdapter___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_TraceState_Lean_HasFormat(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___boxed(lean_object*);
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___boxed(lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___boxed(lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_trace(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_4__checkTraceOptionAux___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Trace_1__addNode___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_push(x_2, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_1__addNode___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_1__addNode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Trace_1__addNode(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_2__getResetTraces___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_2__getResetTraces___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Trace_2__getResetTraces___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Trace_2__getResetTraces(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_array_push(x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_3__addTrace___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_3__addTrace___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_3__addTrace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Trace_3__addTrace(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MonadTracerAdapter_trace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
x_12 = l___private_Init_Lean_Trace_3__addTrace___rarg(x_3, x_4, x_11);
return x_12;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_trace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_3);
x_7 = lean_apply_1(x_6, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_trace___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_trace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_trace___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_MonadTracerAdapter_trace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_MonadTracerAdapter_trace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_MonadTracerAdapter_trace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MonadTracerAdapter_trace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Init_Lean_Trace_1__addNode___rarg(x_1, x_2, x_3);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__3), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_box(x_8);
lean_inc(x_7);
x_10 = lean_apply_1(x_7, x_9);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
lean_inc(x_2);
x_13 = l___private_Init_Lean_Trace_2__getResetTraces___rarg(x_2, x_1);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__4), 6, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_4);
x_8 = lean_apply_1(x_7, x_4);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5___boxed), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_4);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MonadTracerAdapter_traceCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__1), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_inc(x_4);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_4);
x_11 = lean_apply_3(x_7, lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Init_Lean_Trace_1__addNode___rarg(x_1, x_2, x_3);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg___lambda__3), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
lean_inc(x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__3), 6, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_5);
x_12 = lean_apply_3(x_8, lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = 1;
x_10 = lean_box(x_9);
lean_inc(x_8);
x_11 = lean_apply_1(x_8, x_10);
lean_inc(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
lean_inc(x_3);
x_14 = l___private_Init_Lean_Trace_2__getResetTraces___rarg(x_3, x_1);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__4), 7, 6);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_5);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_5);
x_9 = lean_apply_1(x_8, x_5);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_MonadTracerAdapter_traceCtxExcept___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_MonadTracerAdapter_traceCtxExcept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MonadTracerAdapter_traceCtxExcept(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_monadTracerAdapter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtx___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_trace___rarg), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_Lean_monadTracerAdapter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_monadTracerAdapter___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_monadTracerAdapter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_monadTracerAdapter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_monadTracerAdapterExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_traceCtxExcept___rarg), 6, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_MonadTracerAdapter_trace___rarg), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_monadTracerAdapterExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_monadTracerAdapterExcept___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_monadTracerAdapterExcept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_monadTracerAdapterExcept(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TraceState_Inhabited___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Array_empty___closed__1;
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
lean_object* l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_4);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = l_Lean_MessageData_formatAux___main(x_13, x_8);
x_15 = 0;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_4 = x_12;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = 0;
lean_inc(x_2);
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_MessageData_formatAux___main(x_20, x_8);
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_18);
x_4 = x_12;
x_5 = x_22;
goto _start;
}
}
}
}
lean_object* l_Lean_Format_joinArraySep___at_Lean_TraceState_Lean_HasFormat___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(x_1, x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_TraceState_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(x_2, x_3, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Format_joinArraySep___at_Lean_TraceState_Lean_HasFormat___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinArraySep___at_Lean_TraceState_Lean_HasFormat___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TraceState_Lean_HasFormat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TraceState_Lean_HasFormat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = l_Array_iterateMAux___main___at_Lean_TraceState_Lean_HasFormat___spec__2(x_2, x_3, x_2, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_TraceState_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TraceState_HasToString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_TraceState_HasToString___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_TraceState_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TraceState_HasToString___closed__2;
return x_1;
}
}
lean_object* l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_fmt___at_Lean_TraceState_HasToString___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_Trace_4__checkTraceOptionAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Trace_4__checkTraceOptionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Trace_4__checkTraceOptionAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Trace_4__checkTraceOptionAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isEmpty___rarg(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Init_Lean_Trace_4__checkTraceOptionAux___main(x_3, x_2);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Trace_5__checkTraceOption___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Trace_5__checkTraceOption___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Trace_5__checkTraceOption(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace");
return x_1;
}
}
lean_object* _init_l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_12 = l_Lean_Name_append___main(x_11, x_2);
x_13 = l___private_Init_Lean_Trace_5__checkTraceOption___rarg(x_1, x_3, x_12);
return x_13;
}
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1(uint8_t x_1, lean_object* x_2) {
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
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___lambda__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_enableTracing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimpleMonadTracerAdapter_enableTracing(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_getTraces___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SimpleMonadTracerAdapter_getTraces(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SimpleMonadTracerAdapter_modifyTraces___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimpleMonadTracerAdapter_modifyTraces(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_simpleMonadTracerAdapter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_enableTracing___rarg___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_modifyTraces___rarg), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
lean_object* l_Lean_simpleMonadTracerAdapter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_simpleMonadTracerAdapter___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_simpleMonadTracerAdapter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_simpleMonadTracerAdapter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Message(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Trace(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TraceState_Inhabited___closed__1 = _init_l_Lean_TraceState_Inhabited___closed__1();
lean_mark_persistent(l_Lean_TraceState_Inhabited___closed__1);
l_Lean_TraceState_Inhabited = _init_l_Lean_TraceState_Inhabited();
lean_mark_persistent(l_Lean_TraceState_Inhabited);
l_Lean_TraceState_HasToString___closed__1 = _init_l_Lean_TraceState_HasToString___closed__1();
lean_mark_persistent(l_Lean_TraceState_HasToString___closed__1);
l_Lean_TraceState_HasToString___closed__2 = _init_l_Lean_TraceState_HasToString___closed__2();
lean_mark_persistent(l_Lean_TraceState_HasToString___closed__2);
l_Lean_TraceState_HasToString = _init_l_Lean_TraceState_HasToString();
lean_mark_persistent(l_Lean_TraceState_HasToString);
l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1 = _init_l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__1);
l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2 = _init_l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
