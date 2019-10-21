// Lean compiler output
// Module: Init.Util
// Imports: Init.Data.String.Basic Init.Data.ToString
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
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_panicWithPos___rarg___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_dbgSleep___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos(lean_object*);
lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_dbgTraceIfShared___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgSleep(lean_object*, uint32_t, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_dbgTraceIfShared(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace(x_2, x_3);
return x_4;
}
}
lean_object* l_dbgTraceIfShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace_if_shared(x_2, x_3);
return x_4;
}
}
lean_object* l_dbgSleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_dbg_sleep(x_4, x_3);
return x_5;
}
}
lean_object* l_unsafeCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = x_4;
return x_5;
}
}
lean_object* l_panic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_3);
return x_4;
}
}
lean_object* _init_l_panicWithPos___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PANIC at ");
return x_1;
}
}
lean_object* _init_l_panicWithPos___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
lean_object* _init_l_panicWithPos___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": ");
return x_1;
}
}
lean_object* l_panicWithPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_2);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_4);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_5);
x_19 = lean_panic_fn(x_18);
return x_19;
}
}
lean_object* l_panicWithPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panicWithPos___rarg___closed__1 = _init_l_panicWithPos___rarg___closed__1();
lean_mark_persistent(l_panicWithPos___rarg___closed__1);
l_panicWithPos___rarg___closed__2 = _init_l_panicWithPos___rarg___closed__2();
lean_mark_persistent(l_panicWithPos___rarg___closed__2);
l_panicWithPos___rarg___closed__3 = _init_l_panicWithPos___rarg___closed__3();
lean_mark_persistent(l_panicWithPos___rarg___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
