// Lean compiler output
// Module: Init.Util
// Imports: Init.Data.String.Basic Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_dbgSleep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Util_0__mkPanicMessage___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Init_Util_0__mkPanicMessage___closed__2;
LEAN_EXPORT uint8_t l_ptrEq___rarg(lean_object*, lean_object*);
lean_object* lean_dbg_trace_if_shared(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Util_0__mkPanicMessage___closed__1;
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal(lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl(lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_is_exclusive_obj(lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEq(lean_object*);
LEAN_EXPORT lean_object* l_isExclusiveUnsafe___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1;
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEqList(lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTrace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEqList___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTrace___boxed(lean_object*, lean_object*);
lean_object* lean_dbg_stack_trace(lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceIfShared___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrAddrUnsafe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq(lean_object*);
LEAN_EXPORT lean_object* l_ptrEq___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_dbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_dbg_trace(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_dbgTraceVal___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_dbgTraceIfShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_dbg_trace_if_shared(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_dbgStackTrace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_dbg_stack_trace(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_dbgSleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_dbg_sleep(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Init_Util_0__mkPanicMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PANIC at ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_Util_0__mkPanicMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Util_0__mkPanicMessage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l___private_Init_Util_0__mkPanicMessage___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l___private_Init_Util_0__mkPanicMessage___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_7);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l___private_Init_Util_0__mkPanicMessage___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Util_0__mkPanicMessage(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Init_Util_0__mkPanicMessage(x_2, x_3, x_4, x_5);
x_7 = l_panic___rarg(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panicWithPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = l___private_Init_Util_0__mkPanicMessage___closed__1;
x_7 = lean_string_append(x_6, x_2);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_1);
x_11 = l___private_Init_Util_0__mkPanicMessage___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l___private_Init_Util_0__mkPanicMessage___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_2, x_3, x_4, x_5, x_6);
x_8 = l_panic___rarg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPosWithDecl___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPosWithDecl___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ptrAddrUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_isExclusiveUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_exclusive_obj(x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ptr_addr(x_1);
x_5 = lean_box_usize(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_withPtrAddrUnsafe___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_withPtrAddrUnsafe___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_ptrEq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ptrEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ptrEq___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ptrEq___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ptrEq___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_ptrEqList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ptr_addr(x_6);
x_11 = lean_ptr_addr(x_8);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ptrEqList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ptrEqList___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ptrEqList___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ptrEqList___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; 
x_5 = lean_ptr_addr(x_1);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = 1;
x_11 = lean_box(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_withPtrEqUnsafe___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_withPtrEqUnsafe___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; 
x_4 = lean_ptr_addr(x_1);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = 1;
x_10 = lean_box(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_withPtrEqDecEq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_withPtrEqDecEq___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Util_0__mkPanicMessage___closed__1 = _init_l___private_Init_Util_0__mkPanicMessage___closed__1();
lean_mark_persistent(l___private_Init_Util_0__mkPanicMessage___closed__1);
l___private_Init_Util_0__mkPanicMessage___closed__2 = _init_l___private_Init_Util_0__mkPanicMessage___closed__2();
lean_mark_persistent(l___private_Init_Util_0__mkPanicMessage___closed__2);
l___private_Init_Util_0__mkPanicMessage___closed__3 = _init_l___private_Init_Util_0__mkPanicMessage___closed__3();
lean_mark_persistent(l___private_Init_Util_0__mkPanicMessage___closed__3);
l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1 = _init_l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1();
lean_mark_persistent(l___private_Init_Util_0__mkPanicMessageWithDecl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
